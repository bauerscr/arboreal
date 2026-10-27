import Loc.EstPath

/-!
# Test functions vanishing on the diagonal

If `U` vanishes on sequences with a repeated entry (e.g. `U` antisymmetric), and `w` contains
two pairs of entries of equal spin (at positions `i₁ ≠ i₂` with spin `σ` and `k₁ ≠ k₂` with spin
`-σ`), then `U` and its first derivatives at `w` are small when the points of `w` are close:
`‖U(w)‖ ≤ (2dr)^2 K ε^2` and `‖∇U(w)‖ ≤ 2dr K ε^2`, if all derivatives of order `k` of `U` are
bounded by `K ε^k` and the points of `w` lie in the box of radius `r`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d : ℕ}

theorem supNormZ_sub_le {r : ℕ} {a b : Zd d} (ha : supNormZ a ≤ r) (hb : supNormZ b ≤ r) :
    supNormZ (a - b) ≤ 2 * r := by
  rw [supNormZ_le_iff]
  intro i
  have h1 := (supNormZ_le_iff a r).1 ha i
  have h2 := (supNormZ_le_iff b r).1 hb i
  have := Int.natAbs_sub_le (a i) (b i)
  simp only [Pi.sub_apply]
  omega

theorem norm1_sub_le {r : ℕ} {a b : Zd d} (ha : supNormZ a ≤ r) (hb : supNormZ b ≤ r) :
    norm1 (a - b) ≤ ((2 * d * r : ℕ) : ℝ) := by
  calc norm1 (a - b) ≤ d * supNormZ (a - b) := norm1_le _
    _ ≤ d * ((2 * r : ℕ) : ℝ) := by
        gcongr; exact_mod_cast supNormZ_sub_le ha hb
    _ = _ := by push_cast; ring

/-- Path estimate in one entry: if `V` vanishes when the `k₂`-th entry is moved onto the
`k₁`-th one, then `‖V w‖ ≤ ‖w_{k₂} - w_{k₁}‖_1 B`. -/
theorem path_entry {n : ℕ} (V : (Fin n → Sf (Zd d)) → ℂ) {B : ℝ} (k₁ k₂ : Fin n)
    (w : Fin n → Sf (Zd d)) (hsk : (w k₁).2 = (w k₂).2)
    (hV : V (Function.update w k₂ (w k₁)) = 0)
    (hB : ∀ (t : Zd d) (i : Fin d),
      ‖ediff sh k₂ (Sum.inl i : Dir d) V (Function.update w k₂ (t, (w k₂).2))‖ ≤ B) :
    ‖V w‖ ≤ norm1 ((w k₂).1 - (w k₁).1) * B := by
  let f : Zd d → ℂ := fun t => V (Function.update w k₂ (t, (w k₂).2))
  have hf := path_bound f (M := B) (fun t i => by
    have := hB t i
    simp only [ediff, Function.update_self, Function.update_idem] at this
    simp only [f]
    convert this using 4
    simp [sh, single_vaddZ, dirZ]) (w k₂).1 (w k₁).1
  have e1 : f (w k₂).1 = V w := by
    simp only [f, Prod.mk.eta, Function.update_eq_self]
  have e2 : f (w k₁).1 = 0 := by
    simp only [f, ← hsk, hV]
  rwa [e1, e2, sub_zero] at hf

theorem mabs_single_add_single_le {n : ℕ} {j k : Fin n} (hjk : j ≠ k) (e e' : Dir d) (m : Fin n) :
    Grassmann.mabs ((Pi.single j (Pi.single e 1) + Pi.single k (Pi.single e' 1) :
      Fin n → Dir d → ℕ) m) ≤ 1 := by
  rw [Pi.add_apply, mabs_add]
  by_cases hm : m = j
  · subst hm; simp [hjk, Grassmann.mabs]
  · by_cases hm' : m = k
    · subst hm'; simp [hm, Grassmann.mabs]
    · simp [hm, hm', Grassmann.mabs]

theorem ord_single_add_single {n : ℕ} (j k : Fin n) (e e' : Dir d) :
    ord (Pi.single j (Pi.single e 1) + Pi.single k (Pi.single e' 1) : Fin n → Dir d → ℕ) = 2 := by
  rw [ord_add, ord_single, ord_single]

section Bounds

variable {n : ℕ} (U : (Fin n → Sf (Zd d)) → ℂ) {K ε : ℝ} {P : ℕ} (hP : 1 ≤ P)
    (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hU0 : ∀ w : Fin n → Sf (Zd d), ¬Function.Injective w → U w = 0)
    (hUb : ∀ (w : Fin n → Sf (Zd d)) (γ : Fin n → Dir d → ℕ), (∀ k, mabs (γ k) ≤ P) →
      ‖nab γ U w‖ ≤ K * ε ^ ord γ)
include hP hK hε hU0 hUb

omit hP hK hε hU0 hUb in
theorem shZ_add (b b' : Dir d → ℕ) (a : Sf (Zd d)) : sh (b + b') a = sh b (sh b' a) := by
  simp [sh, add_vadd]

omit hP hK hε hU0 hUb in
theorem ediff_eq_nab (j : Fin n) (e : Dir d) :
    ediff sh j e U = nab (Pi.single j (Pi.single e 1)) U :=
  (nabla_single sh (fun _ => sh_zero _) shZ_add j e U).symm

/-- First derivatives in a direction `j` away from a pair of entries of equal spin. -/
theorem ediff_bound {w : Fin n → Sf (Zd d)} {a₁ a₂ : Fin n} (ha : a₁ ≠ a₂)
    (hs : (w a₁).2 = (w a₂).2) {r : ℕ} (hr1 : supNormZ (w a₁).1 ≤ r)
    (hr2 : supNormZ (w a₂).1 ≤ r) {j : Fin n} (hj1 : j ≠ a₁) (hj2 : j ≠ a₂) (e : Dir d) :
    ‖ediff sh j e U w‖ ≤ ((2 * d * r : ℕ) : ℝ) * (K * ε ^ 2) := by
  have hB : 0 ≤ K * ε ^ 2 := by positivity
  have h := path_entry (ediff sh j e U) (B := K * ε ^ 2) a₁ a₂ w hs ?_ ?_
  · exact h.trans (mul_le_mul_of_nonneg_right (norm1_sub_le hr2 hr1) hB)
  · simp only [ediff]
    rw [hU0 _ ?_, hU0 _ ?_, sub_zero]
    · exact fun h => ha (h (by simp [ha]))
    · exact fun h => ha (h (by simp [ha, hj1.symm, hj2.symm]))
  · intro t i
    rw [ediff_eq_nab U, ediff_nabla sh shZ_add]
    refine (hUb _ _ fun m => (mabs_single_add_single_le hj2 _ _ m).trans hP).trans ?_
    rw [ord_single_add_single]

/-- The value at `w`, with two pairs of entries of equal spin. -/
theorem value_bound {w : Fin n → Sf (Zd d)} {i₁ i₂ k₁ k₂ : Fin n} (hi : i₁ ≠ i₂) (hk : k₁ ≠ k₂)
    (hsi : (w i₁).2 = (w i₂).2) (hsk : (w k₁).2 = (w k₂).2) (hik : (w i₁).2 ≠ (w k₁).2)
    {r : ℕ} (hr : ∀ k, supNormZ (w k).1 ≤ r) :
    ‖U w‖ ≤ ((2 * d * r : ℕ) : ℝ) * (((2 * d * r : ℕ) : ℝ) * (K * ε ^ 2)) := by
  have h21 : i₂ ≠ k₁ := fun h => hik (by rw [hsi, h])
  have h22 : i₂ ≠ k₂ := fun h => hik (by rw [hsi, h, hsk])
  have h := path_entry U (B := ((2 * d * r : ℕ) : ℝ) * (K * ε ^ 2)) i₁ i₂ w hsi
    (hU0 _ fun h => hi (h (by simp [hi]))) ?_
  · exact h.trans (mul_le_mul_of_nonneg_right (norm1_sub_le (hr _) (hr _)) (by positivity))
  · intro t i
    exact ediff_bound U hP hK hε hU0 hUb hk (by simpa [Function.update_apply, h21.symm, h22.symm]
      using hsk) (by simpa [Function.update_apply, h21.symm] using hr k₁)
      (by simpa [Function.update_apply, h22.symm] using hr k₂) h21 h22 _

end Bounds

theorem vanish_bound {n : ℕ} (U : (Fin n → Sf (Zd d)) → ℂ) {K ε : ℝ} {P : ℕ} (hP : 1 ≤ P)
    (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hU0 : ∀ w : Fin n → Sf (Zd d), ¬Function.Injective w → U w = 0)
    (hUb : ∀ (w : Fin n → Sf (Zd d)) (γ : Fin n → Dir d → ℕ), (∀ k, mabs (γ k) ≤ P) →
      ‖nab γ U w‖ ≤ K * ε ^ ord γ)
    {w : Fin n → Sf (Zd d)} {i₁ i₂ k₁ k₂ : Fin n} (hi : i₁ ≠ i₂) (hk : k₁ ≠ k₂)
    (hsi : (w i₁).2 = (w i₂).2) (hsk : (w k₁).2 = (w k₂).2) (hik : (w i₁).2 ≠ (w k₁).2)
    {r : ℕ} (hr : ∀ k, supNormZ (w k).1 ≤ r) (γ : Fin n → Dir d → ℕ)
    (hγ : ∀ k, mabs (γ k) ≤ P) :
    ‖nab γ U w‖ ≤ K * ((2 * d * r : ℕ) : ℝ) ^ (2 - min (ord γ) 2) * ε ^ (max (ord γ) 2) := by
  have h11 : i₁ ≠ k₁ := fun h => hik (by rw [h])
  have h12 : i₁ ≠ k₂ := fun h => hik (by rw [h, hsk])
  have h21 : i₂ ≠ k₁ := fun h => hik (by rw [hsi, h])
  have h22 : i₂ ≠ k₂ := fun h => hik (by rw [hsi, h, hsk])
  rcases Nat.lt_or_ge (ord γ) 2 with h | h
  · obtain h0 | h1 : ord γ = 0 ∨ ord γ = 1 := by omega
    · have hγ0 := ord_eq_zero h0
      subst hγ0
      rw [h0, show nab (0 : Fin n → Dir d → ℕ) U = U from nabla_zero sh (fun _ => sh_zero _) U]
      calc ‖U w‖ ≤ _ := value_bound U hP hK hε hU0 hUb hi hk hsi hsk hik hr
        _ = _ := by simp; ring
    · obtain ⟨j, e, rfl⟩ := eq_single_of_ord_eq_one h1
      rw [h1, ← ediff_eq_nab U]
      have : ((2 * d * r : ℕ) : ℝ) * (K * ε ^ 2) =
          K * ((2 * d * r : ℕ) : ℝ) ^ (2 - min 1 2) * ε ^ (max 1 2) := by simp; ring
      rw [← this]
      by_cases hj : j = k₁ ∨ j = k₂
      · rcases hj with rfl | rfl
        · exact ediff_bound U hP hK hε hU0 hUb hi hsi (hr _) (hr _) h11.symm h21.symm e
        · exact ediff_bound U hP hK hε hU0 hUb hi hsi (hr _) (hr _) h12.symm h22.symm e
      · push Not at hj
        exact ediff_bound U hP hK hε hU0 hUb hk hsk (hr _) (hr _) hj.1 hj.2 e
  · rw [min_eq_right h, max_eq_left h, Nat.sub_self, pow_zero, mul_one]
    exact hUb w γ hγ

end

end Loc
