import Step2.D2.D2HV2

/-!
# Lattice differences of `cKer` from the torus derivative bounds

For a torus symbol `w` with `rng w ≤ R`, `2(R + 4) < L^N`, and `x = prj u`, `|u|_∞ ≤ R + 2`:

* `dd0 (cKer R w) u = -∇^{A₀} kern w (x)`, `A₀ = e₀ + ē₀`, and similarly for `Δ₁`, `Δ₀²`, `Λ²`,
  `∂₀Λ` (`ops_cKer`);
* `scaleZ_cKer`: if `|∇^α kern w| ≤ M ρ^{-|α|}` for `|α| ≤ 4`, then `cKer R w` satisfies the
  hypotheses of `bubX_bound1` with `B₂ = M/ρ²`, `B₃ = 4M/ρ³`, `B₄ = 4M/ρ⁴`.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann

variable {L N : ℕ} [NeZero L]

local notation "Λ2" => Lam 2 L N

/-- `char m y` as a unit-modulus character: `char m (p • y) = (char m y)^p`. -/
theorem char_zsmul (m y : Λ2) : ∀ p : ℤ, char m (p • y) = (char m y) ^ p := by
  have hnat : ∀ k : ℕ, char m ((k : ℤ) • y) = (char m y) ^ (k : ℤ) := by
    intro k
    induction k with
    | zero => simp [char_zero_right]
    | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℤ) • y = ((k : ℤ) • y) + y by push_cast; rw [add_smul, one_smul],
        char_add_right, ih]
      rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring]
      rw [zpow_add_one₀ (by
        intro h; have := norm_char m y; rw [h, norm_zero] at this; norm_num at this)]
  have hne : char m y ≠ 0 := by
    intro h; have := norm_char m y; rw [h, norm_zero] at this; norm_num at this
  intro p
  rcases Int.eq_nat_or_neg p with ⟨k, rfl | rfl⟩
  · exact hnat k
  · have h1 : char m ((k : ℤ) • y) * char m ((-(k : ℤ)) • y) = 1 := by
      rw [← char_add_right, ← add_smul, add_neg_cancel, zero_smul, char_zero_right]
    rw [hnat k] at h1
    rw [zpow_neg]
    exact (eq_inv_of_mul_eq_one_right h1)

/-- The unit directions. -/
abbrev e0 : Λ2 := dirVec (Sum.inl 0)
abbrev e1 : Λ2 := dirVec (Sum.inl 1)

theorem prj_zd_pair (p q : ℤ) : (prj (zd (p, q)) : Λ2) = p • (e0 (L := L) (N := N)) + q • e1 := by
  funext i
  fin_cases i <;> simp only [prj, zd, dirVec] <;> erw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply] <;> simp

theorem char_inr (m : Λ2) (i : Fin 2) :
    char m (dirVec (Sum.inr i) : Λ2) = (char m (dirVec (Sum.inl i))) ⁻¹ := by
  have h : char m (dirVec (Sum.inl i) : Λ2) * char m (dirVec (Sum.inr i)) = 1 := by
    rw [← char_add_right, dirVec_inr_eq, add_neg_cancel, char_zero_right]
  exact (eq_inv_of_mul_eq_one_right h)

theorem char_ne_zero (m y : Λ2) : char m y ≠ 0 := by
  intro h; have := norm_char m y; rw [h, norm_zero] at this; norm_num at this

/-- The values of `cKer` near `u` as a Fourier sum. -/
def phiK (w : DressedFRD.Sym 2 (L ^ N)) (x : Λ2) (p q : ℤ) : ℂ :=
  (((L ^ N : ℕ) : ℂ) ^ 2)⁻¹ * ∑ m, w m * char m x * (char m e0) ^ p * (char m e1) ^ q

theorem cKer_near {R : ℕ} {w : DressedFRD.Sym 2 (L ^ N)} (hR : DressedFRD.rng w ≤ R)
    (hn : 2 * (R + 4) < L ^ N) {u : ℤ × ℤ} (hu : nm u ≤ R + 2) (v : ℤ × ℤ)
    (hv : nm (v.1 - u.1, v.2 - u.2) ≤ 2) :
    cKer R w v = phiK w (prj (zd u)) (v.1 - u.1) (v.2 - u.2) := by
  have hvn : nm v ≤ R + 4 := by
    have := nm_add_le u (v.1 - u.1, v.2 - u.2)
    have e : u + (v.1 - u.1, v.2 - u.2) = v := by ext <;> simp
    rw [e] at this; omega
  rw [cKer_eq_kern hR hn hvn]
  have e : zd v = zd u + zd (v.1 - u.1, v.2 - u.2) := by
    rw [← zd_add]; congr 1; ext <;> simp
  rw [e, prj_add, prj_zd_pair (v.1 - u.1) (v.2 - u.2)]
  unfold phiK DressedFRD.kern
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [char_add_right, char_add_right, char_zsmul, char_zsmul]; ring

theorem cKer_far {R : ℕ} {w : DressedFRD.Sym 2 (L ^ N)} {u : ℤ × ℤ} (hu : R + 2 < nm u)
    (v : ℤ × ℤ) (hv : nm (v.1 - u.1, v.2 - u.2) ≤ 2) : cKer R w v = 0 := by
  refine cKer_range w ?_
  have := nm_add_le v (u.1 - v.1, u.2 - v.2)
  have e : v + (u.1 - v.1, u.2 - v.2) = u := by ext <;> simp
  have h2 : nm (u.1 - v.1, u.2 - v.2) = nm (v.1 - u.1, v.2 - u.2) := by
    unfold nm; simp only; rw [show u.1 - v.1 = -(v.1 - u.1) by ring,
      show u.2 - v.2 = -(v.2 - u.2) by ring, Int.natAbs_neg, Int.natAbs_neg]
  rw [e, h2] at this; omega

/-! ### The derivative multi-indices -/

/-- `Δ_i ↔ -σ_{Aᵢ}`, `Aᵢ = eᵢ + ēᵢ`. -/
def Ai (i : Fin 2) : Dir 2 → ℕ := Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1

def E0 : Dir 2 → ℕ := Pi.single (Sum.inl 0) 1
def F0 : Dir 2 → ℕ := Pi.single (Sum.inr 0) 1

theorem sigma_eval (α : Dir 2 → ℕ) (m : Λ2) :
    DressedFRD.sigma α m = (char m e0 - 1) ^ α (Sum.inl 0) * (char m e1 - 1) ^ α (Sum.inl 1) *
      ((char m e0)⁻¹ - 1) ^ α (Sum.inr 0) * ((char m e1)⁻¹ - 1) ^ α (Sum.inr 1) := by
  unfold DressedFRD.sigma
  rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two, char_inr, char_inr]
  ring

/-- `dop α (kern w) x` as a Fourier sum. -/
theorem dop_eval (α : Dir 2 → ℕ) (w : DressedFRD.Sym 2 (L ^ N)) (x : Λ2) :
    dop α (DressedFRD.kern w) x = (((L ^ N : ℕ) : ℂ) ^ 2)⁻¹ *
      ∑ m, w m * char m x * DressedFRD.sigma α m := by
  rw [DressedFRD.dop_kern]
  unfold DressedFRD.kern
  congr 1
  exact sum_congr rfl fun m _ => by ring

section Ops

variable {R : ℕ} {w : DressedFRD.Sym 2 (L ^ N)} (hR : DressedFRD.rng w ≤ R)
  (hn : 2 * (R + 4) < L ^ N) {u : ℤ × ℤ} (hu : nm u ≤ R + 2)
include hR hn hu

theorem dd0_cKer : dd0 (cKer R w) u = -dop (Ai 0) (DressedFRD.kern w) (prj (zd u)) := by
  have hnear := cKer_near hR hn hu
  simp only [dd0]
  simp (disch := (simp only [nm]; ring_nf; decide)) only [hnear]
  ring_nf
  unfold phiK
  rw [dop_eval]
  simp only [mul_sum, sum_mul]
  rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [sigma_eval]
  have hA := char_ne_zero m (e0 (L := L) (N := N))
  simp [Ai, Pi.single_apply]
  field_simp
  ring

theorem dd1_cKer : dd1 (cKer R w) u = -dop (Ai 1) (DressedFRD.kern w) (prj (zd u)) := by
  have hnear := cKer_near hR hn hu
  simp only [dd1]
  simp (disch := (simp only [nm]; ring_nf; decide)) only [hnear]
  ring_nf
  unfold phiK
  simp only [dop_eval]
  simp only [mul_sum, sum_mul, ← sum_sub_distrib, ← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun m _ => ?_
  simp only [sigma_eval]
  have hA := char_ne_zero m (e0 (L := L) (N := N))
  have hB := char_ne_zero m (e1 (L := L) (N := N))
  simp [Ai, E0, F0]
  field_simp
  ring

theorem dd00_cKer : dd0 (dd0 (cKer R w)) u = dop (Ai 0 + Ai 0) (DressedFRD.kern w) (prj (zd u)) := by
  have hnear := cKer_near hR hn hu
  simp only [dd0]
  simp (disch := (simp only [nm]; ring_nf; decide)) only [hnear]
  ring_nf
  unfold phiK
  simp only [dop_eval]
  simp only [mul_sum, sum_mul, ← sum_sub_distrib, ← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun m _ => ?_
  simp only [sigma_eval]
  have hA := char_ne_zero m (e0 (L := L) (N := N))
  have hB := char_ne_zero m (e1 (L := L) (N := N))
  simp [Ai, E0, F0]
  field_simp
  ring

theorem LL_cKer : lapZ (lapZ (cKer R w)) u = dop (Ai 0 + Ai 0) (DressedFRD.kern w) (prj (zd u)) + 2 * dop (Ai 0 + Ai 1) (DressedFRD.kern w) (prj (zd u)) + dop (Ai 1 + Ai 1) (DressedFRD.kern w) (prj (zd u)) := by
  have hnear := cKer_near hR hn hu
  simp only [lapZ, dd0, dd1]
  simp (disch := (simp only [nm]; ring_nf; decide)) only [hnear]
  ring_nf
  unfold phiK
  simp only [dop_eval]
  simp only [mul_sum, sum_mul, ← sum_sub_distrib, ← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun m _ => ?_
  simp only [sigma_eval]
  have hA := char_ne_zero m (e0 (L := L) (N := N))
  have hB := char_ne_zero m (e1 (L := L) (N := N))
  simp [Ai, E0, F0]
  field_simp
  ring

theorem cL_cKer : cd0 (lapZ (cKer R w)) u = -dop (E0 + Ai 0) (DressedFRD.kern w) (prj (zd u)) - dop (E0 + Ai 1) (DressedFRD.kern w) (prj (zd u)) + dop (F0 + Ai 0) (DressedFRD.kern w) (prj (zd u)) + dop (F0 + Ai 1) (DressedFRD.kern w) (prj (zd u)) := by
  have hnear := cKer_near hR hn hu
  simp only [cd0, lapZ, dd0, dd1]
  simp (disch := (simp only [nm]; ring_nf; decide)) only [hnear]
  ring_nf
  unfold phiK
  simp only [dop_eval]
  simp only [mul_sum, sum_mul, ← sum_sub_distrib, ← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun m _ => ?_
  simp only [sigma_eval]
  have hA := char_ne_zero m (e0 (L := L) (N := N))
  have hB := char_ne_zero m (e1 (L := L) (N := N))
  simp [Ai, E0, F0]
  field_simp
  ring

end Ops

/-- The five operator bounds used by `bubX_bound1`. -/
structure OpsB (c : ℤ × ℤ → ℂ) (B2 B3 B4 : ℝ) : Prop where
  d0 : ∀ u, ‖dd0 c u‖ ≤ B2
  d1 : ∀ u, ‖dd1 c u‖ ≤ B2
  d00 : ∀ u, ‖dd0 (dd0 c) u‖ ≤ B4
  dLL : ∀ u, ‖lapZ (lapZ c) u‖ ≤ B4
  dcL : ∀ u, ‖cd0 (lapZ c) u‖ ≤ B3

theorem bubX_bound1' {a c : ℤ × ℤ → ℂ} {R : ℕ} (haR : ∀ v, R < nm v → a v = 0)
    (hc : Function.HasFiniteSupport c) {B2 B3 B4 : ℝ} (h : OpsB c B2 B3 B4) :
    ‖bubX a c‖ ≤ (∑ v ∈ boxR R, ‖a v‖) * (4 * B2 + B4 + R * (R * B4 + 2 * B3) / 2) :=
  bubX_bound1 haR hc h.d0 h.d1 h.d00 h.dLL h.dcL

theorem mabs_Ai (i : Fin 2) : Grassmann.mabs (Ai i) = 2 := by
  fin_cases i <;> simp [Grassmann.mabs, Ai, Fintype.sum_sum_type, Fin.sum_univ_two, Pi.single_apply]

theorem mabs_AiAj (i j : Fin 2) : Grassmann.mabs (Ai i + Ai j) = 4 := by
  fin_cases i <;> fin_cases j <;>
    simp [Grassmann.mabs, Ai, Fintype.sum_sum_type, Fin.sum_univ_two, Pi.single_apply]

theorem mabs_EAi (i : Fin 2) : Grassmann.mabs (E0 + Ai i) = 3 := by
  fin_cases i <;> simp [Grassmann.mabs, Ai, E0, Fintype.sum_sum_type, Fin.sum_univ_two, Pi.single_apply]

theorem mabs_FAi (i : Fin 2) : Grassmann.mabs (F0 + Ai i) = 3 := by
  fin_cases i <;> simp [Grassmann.mabs, Ai, F0, Fintype.sum_sum_type, Fin.sum_univ_two, Pi.single_apply]

/-- **The operator bounds for `cKer` from the torus derivative bounds.** -/
theorem cKer_opsB {R : ℕ} {w : DressedFRD.Sym 2 (L ^ N)} (hR : DressedFRD.rng w ≤ R)
    (hn : 2 * (R + 4) < L ^ N) {M ρ : ℝ} (hρ : 0 < ρ)
    (hM : ∀ α : Dir 2 → ℕ, Grassmann.mabs α ≤ 4 → ∀ x : Λ2,
      ‖dop α (DressedFRD.kern w) x‖ ≤ M / ρ ^ Grassmann.mabs α) :
    OpsB (cKer R w) (M / ρ ^ 2) (4 * M / ρ ^ 3) (4 * M / ρ ^ 4) := by
  have hM0 : 0 ≤ M := by
    have := hM 0 (by simp [Grassmann.mabs]) 0
    simp [Grassmann.mabs] at this
    exact (norm_nonneg _).trans this
  have b2 : ∀ i x, ‖dop (Ai i) (DressedFRD.kern w) x‖ ≤ M / ρ ^ 2 := fun i x => by
    have := hM (Ai i) (by rw [mabs_Ai]; norm_num) x; rwa [mabs_Ai] at this
  have b4 : ∀ i j x, ‖dop (Ai i + Ai j) (DressedFRD.kern w) x‖ ≤ M / ρ ^ 4 := fun i j x => by
    have := hM (Ai i + Ai j) (by rw [mabs_AiAj]) x; rwa [mabs_AiAj] at this
  have b3e : ∀ i x, ‖dop (E0 + Ai i) (DressedFRD.kern w) x‖ ≤ M / ρ ^ 3 := fun i x => by
    have := hM (E0 + Ai i) (by rw [mabs_EAi]; norm_num) x; rwa [mabs_EAi] at this
  have b3f : ∀ i x, ‖dop (F0 + Ai i) (DressedFRD.kern w) x‖ ≤ M / ρ ^ 3 := fun i x => by
    have := hM (F0 + Ai i) (by rw [mabs_FAi]; norm_num) x; rwa [mabs_FAi] at this
  have hp2 : 0 ≤ M / ρ ^ 2 := by positivity
  have hp3 : 0 ≤ M / ρ ^ 3 := by positivity
  have hp4 : 0 ≤ M / ρ ^ 4 := by positivity
  -- far points
  have far : ∀ u, R + 2 < nm u → dd0 (cKer R w) u = 0 ∧ dd1 (cKer R w) u = 0 ∧
      dd0 (dd0 (cKer R w)) u = 0 ∧ lapZ (lapZ (cKer R w)) u = 0 ∧ cd0 (lapZ (cKer R w)) u = 0 := by
    intro u hu
    have hf := cKer_far (w := w) hu
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [dd0, dd1, lapZ, cd0]
      simp (disch := (simp only [nm]; ring_nf; decide)) only [hf]
      ring
  refine ⟨fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_⟩
  · rcases le_or_gt (nm u) (R + 2) with hu | hu
    · rw [dd0_cKer hR hn hu, norm_neg]; exact b2 0 _
    · rw [(far u hu).1, norm_zero]; exact hp2
  · rcases le_or_gt (nm u) (R + 2) with hu | hu
    · rw [dd1_cKer hR hn hu, norm_neg]; exact b2 1 _
    · rw [(far u hu).2.1, norm_zero]; exact hp2
  · rcases le_or_gt (nm u) (R + 2) with hu | hu
    · rw [dd00_cKer hR hn hu]
      refine (b4 0 0 _).trans ?_
      rw [mul_div_assoc]; linarith
    · rw [(far u hu).2.2.1, norm_zero]; positivity
  · rcases le_or_gt (nm u) (R + 2) with hu | hu
    · rw [LL_cKer hR hn hu]
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
      rw [norm_mul, Complex.norm_ofNat]
      have := b4 0 0 (prj (zd u)); have := b4 0 1 (prj (zd u)); have := b4 1 1 (prj (zd u))
      rw [mul_div_assoc]; linarith
    · rw [(far u hu).2.2.2.1, norm_zero]; positivity
  · rcases le_or_gt (nm u) (R + 2) with hu | hu
    · rw [cL_cKer hR hn hu]
      have h1 := b3e 0 (prj (zd u)); have h2 := b3e 1 (prj (zd u))
      have h3 := b3f 0 (prj (zd u)); have h4 := b3f 1 (prj (zd u))
      calc _ ≤ ‖dop (E0 + Ai 0) (DressedFRD.kern w) (prj (zd u))‖ +
            ‖dop (E0 + Ai 1) (DressedFRD.kern w) (prj (zd u))‖ +
            ‖dop (F0 + Ai 0) (DressedFRD.kern w) (prj (zd u))‖ +
            ‖dop (F0 + Ai 1) (DressedFRD.kern w) (prj (zd u))‖ := by
            refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
            refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
            refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
            rw [norm_neg]
        _ ≤ 4 * M / ρ ^ 3 := by rw [mul_div_assoc]; linarith
    · rw [(far u hu).2.2.2.2, norm_zero]; positivity

end

end Step2