import Step2.Flow.FlowValid
import DressedFRD.ZeroMode

/-!
# The last scale and its zero mode (`h02uv-outline.tex`, Section `sec:corr`, "The last scale")

For the dressed decomposition of `FRD` on `Λ_N` (`n = L^N`) the last step `j = N - 1`
integrates `Γ^int_N = Γ_{N-1}(1 + z_{N-1} A Γ_{N-1})^{-1}`. Its zero mode is of size
`1/(Z_N m²)` and is singular as `m² → 0`. We split

  `C'_N = Z_N Γ^int_N = C'^{≠0}_N + t Q`,   `Q_{xy} = |Λ|^{-1}`,   `t = Z_N Γ^int_N(0)`

(`prop_last`), and show, uniformly in `N ≥ 1`, `m² ∈ (0, L^{-2(N-1)}]`, `|ζ_i| ≤ ζ̄`:

* `C'^{≠0}_N` satisfies `GoodCov2` at scale `N - 1` with the field scale of `prop:C5`, is invariant
  under the lattice symmetries and symmetric; the same for the raw `Γ^{int,≠0}_N` with the extra
  factor `|Z_N|^{-1/2}`;
* `m² t = (1 - ε_{N-1}(0))/(1 - ζ'_{N-1} ε_{N-1}(0))` exactly;
* `|t - t_N| ≤ K |Λ| L^{-(N-1)(d-2)} |ζ|_{≤N-1}`, `t_N = Ĉ_N(0) = FRD.tN` the undressed
  zero-mode variance; and `|t - m^{-2}| ≤ K L^{2N} + K |Λ| L^{-(N-1)(d-2)} |ζ|`;
* `t` and the entries of `C'^{≠0}_N` are holomorphic in `(ζ_0, …, ζ_{N-1})` on the polydisc.

`last_continuousOn`: at fixed `ζ`, `t` and the entries of `C'^{≠0}_N` are continuous in
`m² ∈ (0, L^{-2(N-1)}]`.

`prop_last_d2`: in `d = 2`, `|m² t - 1| ≤ K m² L^{2N}`; so `t = m^{-2}(1 + O(m²|Λ|))`.

`validCov_concrete`, `validLast_concrete` (`d = 2`): the covariance part of `ValidAt` for all
`j + 1 < N` (`validAt_concrete` needs `j + 2 < N`), and its analogue for the nonzero modes at
`j + 1 = N`, with the same `ℓ₀`-shape.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

section SymNz

variable {d n : ℕ} [NeZero n]

theorem symmDual_zero'' (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) :
    symmDual π s (0 : Torus d n) = 0 := by
  funext i
  show _ * (0 : Fin d → ZMod n) _ = (0 : Fin d → ZMod n) i
  simp

theorem symmDual_eq_zero_iff (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) (m : Torus d n) :
    symmDual π s m = 0 ↔ m = 0 := by
  constructor
  · intro h
    rw [← symmDual_zero'' π s] at h
    exact (symmDual_bijective π s).1 h
  · rintro rfl; exact symmDual_zero'' π s

theorem nzP_symMem {w : DressedFRD.Sym d n} (hw : w ∈ symSub) : DressedFRD.nzP w ∈ symSub :=
  fun π s m => by simp only [DressedFRD.nzP, symmDual_eq_zero_iff, hw π s m]

end SymNz

variable {d L N : ℕ} [NeZero L]

/-- `GoodCov2` at the last scale `j + 1 = N` from a bound on `‖w‖_{(j)}` (no range condition). -/
theorem goodCov2_last_of_snorm {q j : ℕ} (hj : j + 1 = N) (hL : 1 ≤ L) (hpq : 2 * pPhi d ≤ q)
    {w : DressedFRD.Sym d (L ^ N)} {κ : ℝ} (hw : DressedFRD.snorm (L : ℝ) q j w ≤ κ) :
    GoodCov2 (d := d) (L := L) (N := N) j
      (Real.sqrt κ * (L : ℝ) ^ (-((j : ℝ) * ((d : ℝ) - 2)) / 2) * (L : ℝ) ^ pPhi d)
      (DressedFRD.kmat w) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  constructor
  · refine ⟨_, inferInstance, inferInstance, DressedFRD.gramF w, DressedFRD.gramG w,
      DressedFRD.kmat_isGram _, ?_⟩
    have hB := DressedFRD.kmat_gramBound (L := (L : ℝ)) (p := pPhi d) hL0 hpq hw
    have hB' := GramBound.rescale (c := (L : ℝ)) (by positivity) (by exact_mod_cast hL) hB
    rw [← pow_succ'] at hB'
    exact hB'
  · intro h; omega

theorem frdC_N_zero (P : PtFamily) (msq : ℝ) :
    DressedFRD.frdC P (d := d) (n := L ^ N) msq L N N 0 = tN P d msq (L : ℝ) N := by
  simp only [DressedFRD.frdC, lt_irrefl, if_false, FRD.wt, tN]
  rw [uhat_zero]

open DressedFRD DressedFRD.Data in
/-- **The last scale.** For the dressed decomposition of `FRD`, at the last step `j + 1 = N`,
`C'_N = Z_N Γ^int_N` splits as `C'^{≠0}_N + t Q`. The nonzero modes are Gram-admissible at
scale `N - 1` uniformly in `m² ∈ (0, L^{-2(N-1)}]`, and the zero-mode coefficient `t` is
explicit, `t = m^{-2} + O(L^{2N} + |Λ| L^{-(N-1)(d-2)} |ζ|)` and `t = t_N + O(|Λ|
L^{-(N-1)(d-2)} |ζ|)`. Everything is holomorphic in `ζ`. -/
theorem prop_last (P : PtFamily) (hd : 2 ≤ d) (hL7 : 7 ≤ L) :
    ∃ cS : ℝ, 0 ≤ cS ∧ ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) (msq : ℝ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ j, j + 1 = N →
      let D₀ : Data d (L ^ N) := ⟨L, N, msq, frdC P msq L N, 0⟩
      DifferentiableOn ℂ (fun z : Fin (j + 1) → ℂ => (D₀.Dz z).Z (j + 1) * (D₀.Dz z).Gint j 0)
        {z | ∀ i, ‖z i‖ < ζbar} ∧
      (∀ x y : Lam d L N, DifferentiableOn ℂ
        (fun z : Fin (j + 1) → ℂ => kmat (nzP ((D₀.Dz z).Z (j + 1) • (D₀.Dz z).Gint j)) x y)
        {z | ∀ i, ‖z i‖ < ζbar}) ∧
      ∀ z : Fin (j + 1) → ℂ, (∀ i, ‖z i‖ ≤ ζbar) →
        (∀ x y : Lam d L N, Cdr (D₀.Dz z) j x y =
          kmat (nzP ((D₀.Dz z).Z (j + 1) • (D₀.Dz z).Gint j)) x y +
            (D₀.Dz z).Z (j + 1) * (D₀.Dz z).Gint j 0 / ((L ^ N : ℕ) : ℂ) ^ d) ∧
        GoodCov2 (d := d) (L := L) (N := N) j (ellDr d L cS K ζbar j)
          (kmat (nzP ((D₀.Dz z).Z (j + 1) • (D₀.Dz z).Gint j))) ∧
        GoodCov2 (d := d) (L := L) (N := N) j
          (Real.sqrt ‖((D₀.Dz z).Z (j + 1))⁻¹‖ * ellDr d L cS K ζbar j)
          (kmat (nzP ((D₀.Dz z).Gint j))) ∧
        CSym (d := d) (L := L) (N := N) (kmat (nzP ((D₀.Dz z).Z (j + 1) • (D₀.Dz z).Gint j))) ∧
        (∀ x y : Lam d L N, kmat (nzP ((D₀.Dz z).Z (j + 1) • (D₀.Dz z).Gint j)) x y =
          kmat (nzP ((D₀.Dz z).Z (j + 1) • (D₀.Dz z).Gint j)) y x) ∧
        (msq : ℂ) * ((D₀.Dz z).Z (j + 1) * (D₀.Dz z).Gint j 0) =
          (1 - (D₀.Dz z).eps j ((D₀.Dz z).tails j) 0) /
            (1 - (D₀.Dz z).zp j * (D₀.Dz z).eps j ((D₀.Dz z).tails j) 0) ∧
        ‖(D₀.Dz z).Z (j + 1) * (D₀.Dz z).Gint j 0 - (tN P d msq (L : ℝ) N : ℂ)‖ ≤
          ((L : ℝ) ^ N) ^ d * (L : ℝ) ^ (-((j : ℝ) * ((d : ℝ) - 2))) * (K * (D₀.Dz z).Mz (j + 1)) ∧
        ‖(D₀.Dz z).Z (j + 1) * (D₀.Dz z).Gint j 0 - ((1 / msq : ℝ) : ℂ)‖ ≤
          K * (L : ℝ) ^ (2 * N) +
            ((L : ℝ) ^ N) ^ d * (L : ℝ) ^ (-((j : ℝ) * ((d : ℝ) - 2))) *
              (K * (D₀.Dz z).Mz (j + 1)) := by
  have hq : 2 ≤ 2 * pPhi d := by simp only [pPhi]; omega
  set q := 2 * pPhi d
  set M := q + d + 2
  obtain ⟨cS, hcS, hS⟩ := frd_stdFull P (d := d) hd hL7 (q := q) (M := M) (by omega)
  obtain ⟨ζbar, hζ, hζ8, K, hK⟩ := thm_main_hol (d := d) hd hq hL7 (M := M) (by omega) hcS
  obtain ⟨K₀, hK₀⟩ := tN_sub_inv (P := P) (d := d) (by omega)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hK₀0 : 0 ≤ K₀ := by
    obtain ⟨h1, h2⟩ := hK₀ 1 one_pos 1 le_rfl 0
    simp at h2; linarith
  set cS' := cS * (L : ℝ) ^ d * (1 + 2 * 5 ^ d * (Real.pi / 2) ^ (M : ℝ))
  have hcS' : 0 ≤ cS' := by positivity
  set K' := 2 * max K 0 + K₀
  have hK'0 : 0 ≤ K' := by positivity
  have hKK' : 2 * K ≤ K' := by
    have := le_max_left K 0; simp only [K']; linarith
  have hK₀K' : K₀ ≤ K' := by
    have := le_max_right K 0; simp only [K']; linarith
  refine ⟨cS', hcS', ζbar, hζ, hζ8, K', hK'0, ?_⟩
  intro N msq hN hmsq hmsq' j hj D₀
  subst hj
  have hS' := hS (L ^ (j + 1)) (j + 1) msq hN rfl hmsq
  have h := hK (L ^ (j + 1)) D₀ rfl rfl hS' hmsq'
  have hC : ∀ k π s m, D₀.C k (symmDual π s m) = D₀.C k m := fun k π s m =>
    frdC_symm P _ _ _ _ π s m
  -- holomorphy
  have hG := fun m => (h.2 j (by simp only [D₀]; omega) m).1
  have hZ : DifferentiableOn ℂ (fun z : Fin (j + 1) → ℂ => (D₀.Dz z).Z (j + 1))
      {z | ∀ i, ‖z i‖ < ζbar} := fun z₀ _ =>
    (Hol.Z_mem (D := D₀) (z₀ := z₀) (j + 1)).differentiableWithinAt
  refine ⟨hZ.mul (hG 0), fun x y => ?_, fun z hz => ?_⟩
  · simp only [kmat, kern]
    refine (differentiableOn_const _).mul (DifferentiableOn.fun_sum fun m _ => ?_)
    refine DifferentiableOn.mul ?_ (differentiableOn_const _)
    by_cases hm : m = 0
    · simp only [nzP, hm, if_true]; exact differentiableOn_const _
    · simp only [nzP, hm, if_false, Pi.smul_apply, smul_eq_mul]
      exact hZ.mul (hG m)
  -- the bounds at `z`
  have hzi : ∀ i, ‖(D₀.Dz z).ζ i‖ ≤ ζbar := fun i => by
    show ‖Data.ext z i‖ ≤ ζbar
    unfold Data.ext
    split_ifs
    · exact hz _
    · simp [hζ.le]
  set D := D₀.Dz z with hDdef
  have hc := (hK (L ^ (j + 1)) D rfl rfl hS' hmsq').1 hzi j (show j < j + 1 by omega)
  have hDL : D.L = L := rfl
  have hDN : D.N = j + 1 := rfl
  have hDm : D.msq = msq := rfl
  have hDC : D.C = frdC P msq L (j + 1) := rfl
  have hMz : D.Mz (j + 1) ≤ ζbar := Data.Mz_le hζ.le fun i _ => hzi i
  have hMz0 : 0 ≤ D.Mz (j + 1) := Data.Mz_nonneg _
  have hL0' : (0 : ℝ) < D.L := hL0
  -- `Z_j ≠ 0`, `1 + ζ_j ≠ 0`
  have h1ζ : ∀ i, 1 + D.ζ i ≠ 0 := fun i h0 => by
    have h2 : D.ζ i = -1 := by linear_combination h0
    have := hzi i; rw [h2] at this; norm_num at this; linarith
  have hZj : D.Z j ≠ 0 := prod_ne_zero_iff.2 fun i _ => h1ζ i
  -- the bound on `C_N` without zero mode
  have hCN : snorm (L : ℝ) q j (nzP (ofR (D.C (j + 1)))) ≤ cS' := by
    have := snorm_nzP_CN_le (n := L ^ (j + 1)) (N := j + 1) (C := frdC P msq L (j + 1)) hS'
      (by omega) hL7 hN rfl (by omega)
    simp only [Nat.add_sub_cancel] at this
    exact this
  have hgram := hc.last_gram rfl hL0' hCN
  have hC' : ∀ k π s m, D.C k (symmDual π s m) = D.C k m := hC
  have hsym : D.Gint j ∈ symSub := DData.Gint_symMem hC' j
  have hsymZ : nzP (D.Z (j + 1) • D.Gint j) ∈ symSub := nzP_symMem (smul_symMem _ hsym)
  have hcz := hc.last_zero rfl hL0'
  rw [hDC, frdC_N_zero, hDL] at hcz
  have hcz' : ‖D.Z (j + 1) * D.Gint j 0 - (tN P d msq (L : ℝ) (j + 1) : ℂ)‖ ≤
      ((L : ℝ) ^ (j + 1)) ^ d * (L : ℝ) ^ (-((j : ℝ) * ((d : ℝ) - 2))) * (K' * D.Mz (j + 1)) := by
    refine hcz.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hKK' hMz0) (by positivity)))
    push_cast; ring
  refine ⟨fun x y => ?_, ?_, ?_, kmat_CSym hsymZ, kmat_symm hsymZ, ?_, hcz', ?_⟩
  · -- the splitting
    have := kmat_split (D.Z (j + 1) • D.Gint j) x y
    simpa [Cdr, Pi.smul_apply, smul_eq_mul] using this
  · -- `GoodCov2` for `C'^{≠0}_N`
    have hw : snorm (L : ℝ) q j (nzP (D.Z (j + 1) • D.Gint j)) ≤ cS' + K' * ζbar := by
      rw [nzP_smul, snorm_smul hL0]
      refine hgram.trans ?_
      have : 2 * K * D.Mz (j + 1) ≤ K' * ζbar :=
        (mul_le_mul_of_nonneg_right hKK' hMz0).trans (mul_le_mul_of_nonneg_left hMz hK'0)
      linarith
    exact goodCov2_last_of_snorm rfl (by omega) le_rfl hw
  · -- the raw version
    have hZ1 : D.Z (j + 1) ≠ 0 := prod_ne_zero_iff.2 fun i _ => h1ζ i
    have hZn : 0 < ‖D.Z (j + 1)‖ := norm_pos_iff.2 hZ1
    have hw : snorm (L : ℝ) q j (nzP (D.Gint j)) ≤ ‖(D.Z (j + 1))⁻¹‖ * (cS' + K' * ζbar) := by
      rw [norm_inv, ← div_eq_inv_mul, le_div_iff₀ hZn, mul_comm]
      refine hgram.trans ?_
      have : 2 * K * D.Mz (j + 1) ≤ K' * ζbar :=
        (mul_le_mul_of_nonneg_right hKK' hMz0).trans (mul_le_mul_of_nonneg_left hMz hK'0)
      linarith
    have hg := goodCov2_last_of_snorm (d := d) rfl (by omega) le_rfl hw
    refine hg.mono (le_of_eq ?_)
    unfold ellDr
    rw [Real.sqrt_mul (norm_nonneg _)]
    ring
  · -- the exact formula
    have := last_zero_formula hS'.base (D := D) (j := j) rfl hZj (h1ζ j) (hc.den_eps 0)
    simpa [hDm] using this
  · -- `t - 1/m²`
    obtain ⟨h1, h2⟩ := hK₀ msq hmsq L hL1 (j + 1)
    have e : D.Z (j + 1) * D.Gint j 0 - ((1 / msq : ℝ) : ℂ) =
        (D.Z (j + 1) * D.Gint j 0 - (tN P d msq (L : ℝ) (j + 1) : ℂ)) -
          (((1 / msq - tN P d msq (L : ℝ) (j + 1) : ℝ)) : ℂ) := by push_cast; ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg h1]
    have h3 : K₀ * (L : ℝ) ^ (2 * (j + 1)) ≤ K' * (L : ℝ) ^ (2 * (j + 1)) :=
      mul_le_mul_of_nonneg_right hK₀K' (by positivity)
    linarith

/-- **`d = 2`: leading behaviour of the zero mode.** `|m² t - 1| ≤ K m² L^{2N}`, i.e.
`t = Z_N Γ^int_N(0) = m^{-2} (1 + O(m² |Λ|))`, and `|t - t_N| ≤ K L^{2N} |ζ|_{≤N-1}`. -/
theorem prop_last_d2 (P : PtFamily) (hL7 : 7 ≤ L) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) (msq : ℝ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ j, j + 1 = N →
      let D₀ : DressedFRD.Data 2 (L ^ N) := ⟨L, N, msq, DressedFRD.frdC P msq L N, 0⟩
      ∀ z : Fin (j + 1) → ℂ, (∀ i, ‖z i‖ ≤ ζbar) →
        ‖(D₀.Dz z).Z (j + 1) * (D₀.Dz z).Gint j 0 - (tN P 2 msq (L : ℝ) N : ℂ)‖ ≤
          K * (L : ℝ) ^ (2 * N) * (D₀.Dz z).Mz (j + 1) ∧
        ‖(msq : ℂ) * ((D₀.Dz z).Z (j + 1) * (D₀.Dz z).Gint j 0) - 1‖ ≤
          K * msq * (L : ℝ) ^ (2 * N) := by
  obtain ⟨cS, -, ζbar, hζ, hζ8, K, hK0, h⟩ := prop_last (d := 2) (L := L) P le_rfl hL7
  refine ⟨ζbar, hζ, hζ8, K * (1 + ζbar), by positivity, ?_⟩
  intro N msq hN hmsq hmsq' j hj D₀ z hz
  obtain ⟨-, -, h3⟩ := h N msq hN hmsq hmsq' j hj
  obtain ⟨-, -, -, -, -, -, h4, h5⟩ := h3 z hz
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have e : ((L : ℝ) ^ N) ^ 2 * (L : ℝ) ^ (-((j : ℝ) * ((2 : ℕ) - 2 : ℝ))) = (L : ℝ) ^ (2 * N) := by
    rw [show (-((j : ℝ) * ((2 : ℕ) - 2 : ℝ))) = 0 by push_cast; ring, Real.rpow_zero, mul_one,
      ← pow_mul, mul_comm]
  rw [e] at h4 h5
  have hMz0 : 0 ≤ (D₀.Dz z).Mz (j + 1) := DressedFRD.Data.Mz_nonneg _
  have hMz : (D₀.Dz z).Mz (j + 1) ≤ ζbar := DressedFRD.Data.Mz_le hζ.le fun i hi => by
    show ‖DressedFRD.Data.ext z i‖ ≤ ζbar
    unfold DressedFRD.Data.ext; rw [dif_pos hi]; exact hz _
  have hP : 0 ≤ (L : ℝ) ^ (2 * N) := by positivity
  refine ⟨?_, ?_⟩
  · have hK1 : K ≤ K * (1 + ζbar) := le_mul_of_one_le_right hK0 (by linarith)
    calc _ ≤ (L : ℝ) ^ (2 * N) * (K * (D₀.Dz z).Mz (j + 1)) := h4
      _ = K * (L : ℝ) ^ (2 * N) * (D₀.Dz z).Mz (j + 1) := by ring
      _ ≤ K * (1 + ζbar) * (L : ℝ) ^ (2 * N) * (D₀.Dz z).Mz (j + 1) := by gcongr
  · set t := (D₀.Dz z).Z (j + 1) * (D₀.Dz z).Gint j 0
    have e2 : (msq : ℂ) * t - 1 = (msq : ℂ) * (t - ((1 / msq : ℝ) : ℂ)) := by
      have : (msq : ℂ) ≠ 0 := by exact_mod_cast hmsq.ne'
      push_cast; field_simp
    rw [e2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hmsq.le]
    calc msq * ‖t - ((1 / msq : ℝ) : ℂ)‖
        ≤ msq * (K * (L : ℝ) ^ (2 * N) + (L : ℝ) ^ (2 * N) * (K * (D₀.Dz z).Mz (j + 1))) :=
          mul_le_mul_of_nonneg_left h5 hmsq.le
      _ ≤ msq * (K * (L : ℝ) ^ (2 * N) + (L : ℝ) ^ (2 * N) * (K * ζbar)) := by gcongr
      _ = K * (1 + ζbar) * msq * (L : ℝ) ^ (2 * N) := by ring

open MsqCont in
/-- **Continuity in `m²` at the last scale** (fixed `ζ`): the zero-mode coefficient
`t = Z_N Γ^int_N(0)` and the entries of `C'^{≠0}_N` are continuous in `m² ∈ (0, L^{-2(N-1)}]`. -/
theorem last_continuousOn (P : PtFamily) (hd : 2 ≤ d) (hL7 : 7 ≤ L) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∀ (N : ℕ), 1 ≤ N → ∀ ζ : ℕ → ℂ, (∀ i, ‖ζ i‖ ≤ ζbar) →
      ∀ j, j + 1 = N →
        ContinuousOn (fun msq => (Dm P L N ζ msq : DressedFRD.Data d (L ^ N)).Z (j + 1) *
            (Dm P L N ζ msq : DressedFRD.Data d (L ^ N)).Gint j 0)
          (Set.Ioc 0 ((L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))) ∧
        ∀ x y : Lam d L N,
          ContinuousOn (fun msq => DressedFRD.kmat (DressedFRD.nzP
              ((Dm P L N ζ msq : DressedFRD.Data d (L ^ N)).Z (j + 1) •
                (Dm P L N ζ msq : DressedFRD.Data d (L ^ N)).Gint j)) x y)
            (Set.Ioc 0 ((L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))) := by
  have hq : 2 ≤ 2 * pPhi d := by simp only [pPhi]; omega
  obtain ⟨cS, hcS, hS⟩ := DressedFRD.frd_stdFull P (d := d) hd hL7 (q := 2 * pPhi d)
    (M := 2 * pPhi d + d + 1) le_rfl
  obtain ⟨ζbar, hζ, hζ8, K, hK⟩ := DressedFRD.thm_main_full (d := d) hd hq hL7
    (M := 2 * pPhi d + d + 1) le_rfl hcS
  refine ⟨ζbar, hζ, fun N hN ζ hζi j hj => ?_⟩
  have hZ : ∀ k, (∏ i ∈ range k, (1 + ζ i)) ≠ 0 := fun k => prod_ne_zero_iff.2 fun i _ h0 => by
    have h1 : ζ i = -1 := by linear_combination h0
    have := hζi i; rw [h1] at this; norm_num at this; linarith
  have hG : ∀ x₀ ∈ Set.Ioc 0 ((L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))), ∀ m,
      ContinuousAt (fun z => (Dm P L N ζ z : DressedFRD.Data d (L ^ N)).Gint j m) x₀ := by
    intro x₀ hx₀ m
    have hS' := hS (L ^ N) N x₀ hN rfl hx₀.1
    have hc : ∀ k, k < N → (Dm P L N ζ x₀ : DressedFRD.Data d (L ^ N)).Concl (2 * pPhi d) ζbar K k :=
      fun k hk => hK (L ^ N) (Dm P L N ζ x₀) rfl rfl hS' hx₀.2 hζi k hk
    exact Gint_mem (by omega) hx₀.1 hZ (fun k hk m => (hc k (by omega)).den_eps m)
      (fun m => (hc j (by omega)).den m) m
  refine ⟨fun x₀ hx₀ => ?_, fun x y x₀ hx₀ => ?_⟩
  · simp only [MsqCont.Z_eq]
    exact (continuousAt_const.mul (hG x₀ hx₀ 0)).continuousWithinAt
  · refine ContinuousAt.continuousWithinAt ?_
    simp only [DressedFRD.kmat, DressedFRD.kern]
    refine continuousAt_const.mul (tendsto_finsetSum _ fun m _ => ?_)
    refine ContinuousAt.mul ?_ continuousAt_const
    by_cases hm : m = 0
    · simp only [DressedFRD.nzP, hm, if_true]; exact continuousAt_const
    · simp only [DressedFRD.nzP, hm, if_false, Pi.smul_apply, smul_eq_mul, MsqCont.Z_eq]
      exact continuousAt_const.mul (hG x₀ hx₀ m)

/-- **The covariance part of `ValidAt` for all `j + 1 < N`** (`d = 2`). `validAt_concrete`
additionally requires `j + 2 < N`, which is part of the definition of `ValidAt`. -/
theorem validCov_concrete (P : PtFamily) (hL : 2 ^ (2 + 3) + 8 * 2 < L) :
    ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N), R.P = P → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → ℓ₀ ≤ R.ℓ → 0 ≤ R.ρ → R.ρ ≤ ζbar →
      ∀ j, j + 1 < N → ∀ ζ : ℕ → ℂ, (∀ i, ‖ζ i‖ ≤ R.ρ) →
        GoodCov2 j (fscale (∏ i ∈ range (j + 1), (1 + ζ i)) * R.ℓ / 4) (rawCov R j ζ) ∧
        TInv (rawCov R j ζ) ∧ CSym (rawCov R j ζ) ∧ ∀ x y, rawCov R j ζ x y = rawCov R j ζ y x := by
  obtain ⟨cS, hcS, ζbar, hζ, hζ8, K, hK0, h⟩ := raw_family (d := 2) (L := L) P le_rfl (by omega)
  have hE0 : 0 ≤ ellDr 2 L cS K ζbar 0 := by unfold ellDr; positivity
  refine ⟨4 * ellDr 2 L cS K ζbar 0 + 1, by linarith, ζbar, hζ, hζ8, ?_⟩
  intro N R hP hN hm0 hm hℓ hρ0 hρ j hj ζ hζb
  set z : Fin (j + 1) → ℂ := fun i => ζ i
  set D₀ : DressedFRD.Data 2 (L ^ N) := ⟨L, N, R.msq, DressedFRD.frdC P R.msq L N, 0⟩
  have hz : ∀ i, ‖z i‖ ≤ ζbar := fun i => (hζb i).trans hρ
  have hg := h N R.msq hN hm0 hm j hj z hz
  have hDζ : (⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, ζ⟩ : DressedFRD.Data 2 (L ^ N)) =
      D₀.withζ ζ := by rw [hP]; rfl
  have hG : rawCov R j ζ = DressedFRD.kmat ((D₀.Dz z).Gint j) := by
    unfold rawCov
    rw [hDζ]
    have e : D₀.Dz z = (D₀.withζ ζ).withζ (DressedFRD.Data.ext z) := rfl
    rw [e, DressedFRD.Data.Gint_congr (D := D₀.withζ ζ) (ζ' := DressedFRD.Data.ext z)]
    intro i hi
    show ζ i = DressedFRD.Data.ext z i
    unfold DressedFRD.Data.ext
    rw [dif_pos (by omega)]
  have hZ : (D₀.Dz z).Z (j + 1) = ∏ i ∈ range (j + 1), (1 + ζ i) := by
    unfold DressedFRD.Data.Z
    refine prod_congr rfl fun i hi => ?_
    show 1 + DressedFRD.Data.ext z i = 1 + ζ i
    unfold DressedFRD.Data.ext
    rw [dif_pos (mem_range.1 hi)]
  have hC : ∀ k π s m, (D₀.Dz z).C k (symmDual π s m) = (D₀.Dz z).C k m :=
    fun k π s m => frdC_symm P _ _ _ _ π s m
  have hsym : DressedFRD.Data.Gint (D₀.Dz z) j ∈ symSub := DData.Gint_symMem hC j
  rw [hG]
  refine ⟨?_, TInv_kmat _, kmat_CSym hsym, kmat_symm hsym⟩
  refine hg.mono ?_
  rw [hZ, ellDr_two, norm_inv]
  unfold fscale
  have : 0 ≤ Real.sqrt ‖∏ i ∈ range (j + 1), (1 + ζ i)‖⁻¹ := Real.sqrt_nonneg _
  have h4 : ellDr 2 L cS K ζbar 0 ≤ R.ℓ / 4 := by linarith
  calc Real.sqrt ‖∏ i ∈ range (j + 1), (1 + ζ i)‖⁻¹ * ellDr 2 L cS K ζbar 0 ≤
      Real.sqrt ‖∏ i ∈ range (j + 1), (1 + ζ i)‖⁻¹ * (R.ℓ / 4) := by gcongr
    _ = _ := by ring

/-- **The last step, nonzero modes** (`d = 2`): the analogue of the covariance part of
`ValidAt` at `j + 1 = N` for `Γ^{int,≠0}_N` (the raw covariance without its zero mode). -/
theorem validLast_concrete (P : PtFamily) (hL : 2 ^ (2 + 3) + 8 * 2 < L) :
    ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N), R.P = P → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → ℓ₀ ≤ R.ℓ → 0 ≤ R.ρ → R.ρ ≤ ζbar →
      ∀ j, j + 1 = N → ∀ ζ : ℕ → ℂ, (∀ i, ‖ζ i‖ ≤ R.ρ) →
        let C := DressedFRD.kmat (DressedFRD.nzP
          ((⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, ζ⟩ : DressedFRD.Data 2 (L ^ N)).Gint j))
        GoodCov2 j (fscale (∏ i ∈ range (j + 1), (1 + ζ i)) * R.ℓ / 4) C ∧
        TInv C ∧ CSym C ∧ ∀ x y, C x y = C y x := by
  obtain ⟨cS, hcS, ζbar, hζ, hζ8, K, hK0, h⟩ := prop_last (d := 2) (L := L) P le_rfl (by omega)
  have hE0 : 0 ≤ ellDr 2 L cS K ζbar 0 := by unfold ellDr; positivity
  refine ⟨4 * ellDr 2 L cS K ζbar 0 + 1, by linarith, ζbar, hζ, hζ8, ?_⟩
  intro N R hP hN hm0 hm hℓ hρ0 hρ j hj ζ hζb C
  set z : Fin (j + 1) → ℂ := fun i => ζ i
  set D₀ : DressedFRD.Data 2 (L ^ N) := ⟨L, N, R.msq, DressedFRD.frdC P R.msq L N, 0⟩
  have hz : ∀ i, ‖z i‖ ≤ ζbar := fun i => (hζb i).trans hρ
  obtain ⟨-, -, h3⟩ := h N R.msq hN hm0 hm j hj
  obtain ⟨-, -, hg, -, -, -, -, -⟩ := h3 z hz
  have hDζ : (⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, ζ⟩ : DressedFRD.Data 2 (L ^ N)) =
      D₀.withζ ζ := by rw [hP]; rfl
  have hG : C = DressedFRD.kmat (DressedFRD.nzP ((D₀.Dz z).Gint j)) := by
    simp only [C]
    rw [hDζ]
    have e : D₀.Dz z = (D₀.withζ ζ).withζ (DressedFRD.Data.ext z) := rfl
    rw [e, DressedFRD.Data.Gint_congr (D := D₀.withζ ζ) (ζ' := DressedFRD.Data.ext z)]
    intro i hi
    show ζ i = DressedFRD.Data.ext z i
    unfold DressedFRD.Data.ext
    rw [dif_pos (by omega)]
  have hZ : (D₀.Dz z).Z (j + 1) = ∏ i ∈ range (j + 1), (1 + ζ i) := by
    unfold DressedFRD.Data.Z
    refine prod_congr rfl fun i hi => ?_
    show 1 + DressedFRD.Data.ext z i = 1 + ζ i
    unfold DressedFRD.Data.ext
    rw [dif_pos (mem_range.1 hi)]
  have hC : ∀ k π s m, (D₀.Dz z).C k (symmDual π s m) = (D₀.Dz z).C k m :=
    fun k π s m => frdC_symm P _ _ _ _ π s m
  have hsym : DressedFRD.nzP (DressedFRD.Data.Gint (D₀.Dz z) j) ∈ symSub :=
    nzP_symMem (DData.Gint_symMem hC j)
  rw [hG]
  refine ⟨?_, TInv_kmat _, kmat_CSym hsym, kmat_symm hsym⟩
  refine hg.mono ?_
  rw [hZ, ellDr_two]
  unfold fscale
  rw [norm_inv]
  have : 0 ≤ Real.sqrt ‖∏ i ∈ range (j + 1), (1 + ζ i)‖⁻¹ := Real.sqrt_nonneg _
  have h4 : ellDr 2 L cS K ζbar 0 ≤ R.ℓ / 4 := by linarith
  calc Real.sqrt ‖∏ i ∈ range (j + 1), (1 + ζ i)‖⁻¹ * ellDr 2 L cS K ζbar 0 ≤
      Real.sqrt ‖∏ i ∈ range (j + 1), (1 + ζ i)‖⁻¹ * (R.ℓ / 4) := by gcongr
    _ = _ := by ring

end

end Step2
