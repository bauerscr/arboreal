import Step2.D2.D2Bx2
import Step2.D2.D2Past

/-!
# The scale form of the bilinear bound; bilinearity; the individual past coefficients

* `ScaleZ c M ρ`: `c` is of scale `ρ` with amplitude `M` (`|Δᵢ c| ≤ M ρ^{-2}`,
  `|Δ₀Δ₀ c|, |Λ² c| ≤ M ρ^{-4}`, `|∂₀Λ c| ≤ M ρ^{-3}`);
* `bubX_scale`: **if `a` has range `R ≥ 1` and `|a| ≤ M_A`, and `c` is of scale `ρ ≥ 1` with
  amplitude `M_C`, then `|𝔅x(a, c)| ≤ 54 M_A M_C (R/ρ)² (1 + R/ρ)²`** (absolute constant);
* `bubX_add_left`, `bubX_add_right`: bilinearity;
* `FlowSeq.beta_past_bubX`: for `k < j`, `s ≡ 1`, even kernels `c_k`, `c_j` of the (translation
  invariant) covariances, `b_{j,k} = 2 𝔅x(c_k, c_j) + T_{j,k}`, `T_{j,k} = tadT B_+ 0 C_k C_j`.
-/

namespace Step2

open Step

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann

noncomputable section

/-- `c` is of scale `ρ` with amplitude `M`. -/
structure ScaleZ (c : ℤ × ℤ → ℂ) (M ρ : ℝ) : Prop where
  d0 : ∀ u, ‖dd0 c u‖ ≤ M / ρ ^ 2
  d1 : ∀ u, ‖dd1 c u‖ ≤ M / ρ ^ 2
  d00 : ∀ u, ‖dd0 (dd0 c) u‖ ≤ M / ρ ^ 4
  dLL : ∀ u, ‖lapZ (lapZ c) u‖ ≤ M / ρ ^ 4
  dcL : ∀ u, ‖cd0 (lapZ c) u‖ ≤ M / ρ ^ 3

/-- **The bilinear scale bound.** -/
theorem bubX_scale {a c : ℤ × ℤ → ℂ} {R : ℕ} (hR1 : 1 ≤ R) (haR : ∀ v, R < nm v → a v = 0)
    (hc : Function.HasFiniteSupport c) {MA MC ρ : ℝ} (hρ : 1 ≤ ρ) (hMA : ∀ v, ‖a v‖ ≤ MA)
    (hMC : 0 ≤ MC) (hS : ScaleZ c MC ρ) :
    ‖bubX a c‖ ≤ 54 * MA * MC * ((R : ℝ) / ρ) ^ 2 * (1 + (R : ℝ) / ρ) ^ 2 := by
  have hb := bubX_bound haR hc hMA hS.d0 hS.d1 hS.d00 hS.dLL hS.dcL
  have hMA0 : 0 ≤ MA := (norm_nonneg _).trans (hMA 0)
  have hρ0 : 0 < ρ := by linarith
  have hR : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  set x := (R : ℝ) / ρ with hx
  have hx0 : 0 ≤ x := by positivity
  have hRx : (R : ℝ) = x * ρ := by rw [hx]; field_simp
  refine hb.trans ?_
  -- `(2R+1)² ≤ 9R²` and the bracket `≤ 6 (1+x)² / ρ²`
  have h9 : (2 * (R : ℝ) + 1) ^ 2 ≤ 9 * (R : ℝ) ^ 2 := by nlinarith
  have hbr : MA * (4 * (MC / ρ ^ 2) + MC / ρ ^ 4) + R * MA * ((R * (MC / ρ ^ 4) + 2 * (MC / ρ ^ 3)) / 2)
      ≤ MA * MC * (6 * (1 + x) ^ 2) / ρ ^ 2 := by
    have hρ4 : 1 / ρ ^ 4 ≤ 1 / ρ ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ hρ (by norm_num)
    have e : MA * (4 * (MC / ρ ^ 2) + MC / ρ ^ 4) + R * MA * ((R * (MC / ρ ^ 4) + 2 * (MC / ρ ^ 3)) / 2)
        = MA * MC * (4 + 1 / ρ ^ 2 + x ^ 2 / 2 + x) / ρ ^ 2 := by
      rw [hRx]; field_simp; ring
    rw [e]
    have h1 : 1 / ρ ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have : 4 + 1 / ρ ^ 2 + x ^ 2 / 2 + x ≤ 6 * (1 + x) ^ 2 := by nlinarith
    have hpos : 0 ≤ MA * MC := mul_nonneg hMA0 hMC
    rw [div_le_div_iff_of_pos_right (by positivity)]
    exact mul_le_mul_of_nonneg_left this hpos
  calc (2 * (R : ℝ) + 1) ^ 2 * (MA * (4 * (MC / ρ ^ 2) + MC / ρ ^ 4)) +
        (2 * R + 1) ^ 2 * (R * MA * ((R * (MC / ρ ^ 4) + 2 * (MC / ρ ^ 3)) / 2))
      = (2 * (R : ℝ) + 1) ^ 2 * (MA * (4 * (MC / ρ ^ 2) + MC / ρ ^ 4) +
        R * MA * ((R * (MC / ρ ^ 4) + 2 * (MC / ρ ^ 3)) / 2)) := by ring
    _ ≤ (9 * (R : ℝ) ^ 2) * (MA * MC * (6 * (1 + x) ^ 2) / ρ ^ 2) := by
        apply mul_le_mul h9 hbr (by positivity) (by positivity)
    _ = 54 * MA * MC * x ^ 2 * (1 + x) ^ 2 := by rw [hRx]; field_simp; ring

/-! ### Bilinearity -/

theorem symb_add {a a' : ℤ × ℤ → ℂ} (ha : Function.HasFiniteSupport a)
    (ha' : Function.HasFiniteSupport a') (j : ℕ) (p : ℂ) :
    symb (a + a') j p = symb a j p + symb a' j p := by
  unfold symb
  rw [← finsum_add_distrib (hfs_symb a ha j p) (hfs_symb a' ha' j p)]
  refine finsum_congr fun v => ?_
  simp only [Pi.add_apply]; ring

theorem hfs_add {a a' : ℤ × ℤ → ℂ} (ha : Function.HasFiniteSupport a)
    (ha' : Function.HasFiniteSupport a') : Function.HasFiniteSupport (a + a') :=
  Set.Finite.subset (ha.union ha') (Function.support_add _ _)

theorem bubX_add_left {a a' c : ℤ × ℤ → ℂ} (ha : Function.HasFiniteSupport a)
    (ha' : Function.HasFiniteSupport a') (hc : Function.HasFiniteSupport c) :
    bubX (a + a') c = bubX a c + bubX a' c := by
  unfold bubX
  simp only [symb_add ha ha']
  have i1 : ∀ (l : List KCoef) (j : ℕ) (b : ℤ × ℤ → ℂ), Function.HasFiniteSupport b →
      IntegrableOn (fun p => trigK l p * (symb b j p * symb c j p)) BZ := fun l j b hb =>
    ((continuous_trigK l).mul ((continuous_symb b hb j).mul (continuous_symb c hc j))).continuousOn.integrableOn_compact
      isCompact_BZ
  have e : ∀ (l : List KCoef) (j : ℕ), ∫ p in BZ, trigK l p * ((symb a j p + symb a' j p) * symb c j p)
      = (∫ p in BZ, trigK l p * (symb a j p * symb c j p)) +
        ∫ p in BZ, trigK l p * (symb a' j p * symb c j p) := by
    intro l j
    rw [← integral_add (i1 l j a ha) (i1 l j a' ha')]
    congr 1; funext p; ring
  rw [e, e]; ring

theorem bubX_add_right {a c c' : ℤ × ℤ → ℂ} (ha : Function.HasFiniteSupport a)
    (hc : Function.HasFiniteSupport c) (hc' : Function.HasFiniteSupport c') :
    bubX a (c + c') = bubX a c + bubX a c' := by
  rw [bubX_comm, bubX_add_left hc hc' ha, bubX_comm c, bubX_comm c']

/-- `𝔅x(a + a', a + a') = 𝔅x(a, a) + 2 𝔅x(a, a') + 𝔅x(a', a')`. -/
theorem bubX_add_add {a a' : ℤ × ℤ → ℂ} (ha : Function.HasFiniteSupport a)
    (ha' : Function.HasFiniteSupport a') :
    bubX (a + a') (a + a') = bubX a a + 2 * bubX a a' + bubX a' a' := by
  rw [bubX_add_left ha ha' (hfs_add ha ha'), bubX_add_right ha ha ha', bubX_add_right ha' ha ha',
    bubX_comm a' a]; ring

/-! ### The individual past coefficients -/

namespace FlowSeq

variable {L N : ℕ} [NeZero L] (D : FlowSeq 2 L N)

/-- **The individual past coefficients** (`k < j`, `s ≡ 1`, direction `i₀ = 0`):
if `C_k = cTor c_k`, `C_j = cTor c_j` with even `c_k`, `c_j` of range `R`, then
`b_{j,k} = 2 𝔅x(c_k, c_j) + T_{j,k}`. -/
theorem beta_past_bubX (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hs : ∀ i, D.s i = 1) {j k : ℕ} (hkj : k < j)
    (hjN : j + 1 < N) {ℓ : ℝ} (hC : ∀ i, GoodCov2 i ℓ (D.C i)) {b : Fin 2 → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) {R : ℕ} {ck cj : ℤ × ℤ → ℂ}
    (hkR : ∀ u, R < nm u → ck u = 0) (hjR : ∀ u, R < nm u → cj u = 0)
    (hke : ∀ v : ℤ × ℤ, ck (-v.1, -v.2) = ck v) (hje : ∀ v : ℤ × ℤ, cj (-v.1, -v.2) = cj v)
    (hCk : ∀ x y, D.C k x y = cTor ck (x - y)) (hCj : ∀ x y, D.C j x y = cTor cj (x - y))
    (hn : 2 * (R + 4) < L ^ N)
    (hX : ∀ x ∈ Bp (L := L) (N := N) j b,
      2 * (supNorm (x - base (Bp (L := L) (N := N) j b)) + R + 3) < L ^ N) :
    D.beta j k b 0 (eC 3) (eC 3) 3 = 2 * bubX ck cj +
      tadT (Bp (L := L) (N := N) j b) 0 (D.C k) (D.C j) := by
  set X := Bp (L := L) (N := N) j b
  have hne : X.Nonempty := (isSmall_clo (isSmall_blockSet_of_mem hb)).2.1.1
  have hc : (X.card : ℂ) ≠ 0 := by
    have := (isSmall_clo (isSmall_blockSet_of_mem hb)).2.1.1.card_pos
    exact_mod_cast this.ne'
  have hA := even_VcoupL X (eC 3)
  have hB := even_VcoupL (L := L) (N := N) (d := 2) univ (eC 3)
  have hA4 := degLe_VcoupL_eg X
  have hB4 := degLe_VcoupL_eg (L := L) (N := N) (d := 2) univ
  rw [D.beta_past_eq (by norm_num) hL hkj hjN (fun i _ => hC i) hb 0]
  simp only [hs, one_pow, prod_const_one, one_mul, map_smul, mu4_smul]
  rw [mu4_lop_FC_eq _ _ _ _ _ hA hB hA4 hB4]
  -- the three bubbles
  have hck := hfs_of_range ck hkR
  have hcj := hfs_of_range cj hjR
  have hsR : ∀ u, R < nm u → (ck + cj) u = 0 := fun u hu => by
    simp [hkR u hu, hjR u hu]
  have hse : ∀ v : ℤ × ℤ, (ck + cj) (-v.1, -v.2) = (ck + cj) v := fun v => by
    simp [hke v, hje v]
  have b1 := negBub_eq_mu4_FC hL (by omega) hb 0 (D.C k + D.C j)
  have b2 := negBub_eq_mu4_FC hL (by omega) hb 0 (D.C k)
  have b3 := negBub_eq_mu4_FC hL (by omega) hb 0 (D.C j)
  rw [negBub_eq_bubX hsR hse hn (fun x y => by
      rw [Matrix.add_apply, hCk, hCj]; rfl) hne hX] at b1
  rw [negBub_eq_bubX hkR hke hn hCk hne hX] at b2
  rw [negBub_eq_bubX hjR hje hn hCj hne hX] at b3
  rw [bubX_add_add hck hcj] at b1
  rw [eq_div_iff (mul_ne_zero two_ne_zero hc)] at b1 b2 b3
  rw [← b1, ← b2, ← b3, tadT]
  simp only [X] at hc ⊢
  field_simp
  ring

end FlowSeq

end

end Step2
