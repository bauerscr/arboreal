import PtCorr2.Zero.OnePt
import PtCorr.Bridge

/-!
# The two-point function and `⟨z_0z_x⟩` at `h ≥ 0` (model level)

For the ghost arboreal gas (`h ≥ 0`) the `z`-correlation splits into the two-point function and a
ghost term:

  `⟨z_az_x⟩_{β,h} = P_{β,h}[a ↔ g, x ↔ g] - P_{β,h}[a ↔ x, a ↮ g]`   (`avg_zz_split`).

In `ψ`-variables with `V_0 = (0, 0, μ₀, b)`, `β = 1/b`, `h = (μ₀ + m²)/b - 1 ≥ 0`, writing
`z̃_y = 1 - bψ̄_yψ_y`:

  `b⟨ψ̄_0ψ_x⟩ = -⟨z̃_0z̃_x⟩ + p`,  `0 ≤ p ≤ r = 1 - b⟨ψ̄_0ψ_0⟩`   (`twopt_eq_neg_zz`),

and `⟨z̃_x⟩ = ⟨z̃_0⟩ = r` (`avg0_zt_transl`). So the two-point input `Spin2.TwoPtSq` is a statement
about the Case-(2) pair observable `z̃_0z̃_x` (both sources `σ_aσ_b` with `γ = 1`, `μ = -b`) up to the
one-point deficit `r`; this is how the `d = 2` square is set up in `PtCorr2/Pair/TwoPtZZ.lean`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Step2 Step

section Model

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- Additivity of `P` over a disjoint union of events. -/
theorem arborealProb_or_disj {V : Type*} [Fintype V] [DecidableEq V] {β : V → V → ℝ}
    (hβ : ∀ i j, β i j = β j i) (A B C : SimpleGraph V → Prop) (hC : ∀ F, C F ↔ A F ∨ B F)
    (hd : ∀ F, ¬(A F ∧ B F)) :
    H02.arborealProb β hβ C = H02.arborealProb β hβ A + H02.arborealProb β hβ B := by
  classical
  unfold H02.arborealProb
  rw [← add_div]
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun F _ => ?_
  have h1 := hC F
  have h2 := hd F
  by_cases hA : A F <;> by_cases hB : B F <;> by_cases hF : F.IsAcyclic <;> simp_all

/-- **`⟨z_az_x⟩_{β,h} = P[a ↔ g, x ↔ g] - P[a ↔ x, a ↮ g]`** (ghost arboreal gas, `h ≥ 0`). -/
theorem avg_zz_split {w : Λ → Λ → ℝ} (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    {h : Λ → ℝ} (hh : ∀ i, 0 ≤ h i) (a x : Λ) :
    H02.avg w h (H02.z a * H02.z x) =
      H02.arborealProb (H02.ghostW w h) (H02.ghostW_symm hw h)
          (fun F => F.Reachable (some a) none ∧ F.Reachable (some x) none) -
        H02.avg w h (H02.ξ a * H02.η x) := by
  have e1 := H02.arborealProb_ghost_uu hw hw0 hh a x
  have e2 := H02.avg_ξη_add hw h a x
  have e3 := H02.arborealProb_ghost_xieta hw hw0 hh a x
  have e4 := arborealProb_or_disj (H02.ghostW_symm hw h)
    (fun F => (H02.base F).Reachable a x ∧ ¬F.Reachable (some a) none)
    (fun F => F.Reachable (some a) none ∧ F.Reachable (some x) none)
    (fun F => F.Reachable (some a) (some x))
    (fun F => by
      rw [H02.reachable_some_iff]
      constructor
      · rintro (hb | hg)
        · by_cases hA : F.Reachable (some a) none
          · exact Or.inr ⟨hA, ((hb.map (H02.baseHom F)).symm.trans hA)⟩
          · exact Or.inl ⟨hb, hA⟩
        · exact Or.inr hg
      · rintro (hb | hg)
        · exact Or.inl hb.1
        · exact Or.inr hg)
    (fun F h => h.1.2 h.2.1)
  linarith

variable {L N : ℕ} [NeZero L]

omit [NeZero L] in
/-- `z̃_y = 1 - bψ̄_yψ_y`, the image of `z_y` under the bridge with `c² = b`. -/
theorem phiC_zz_eq {b : ℝ} (hb : 0 < b) (a x : Lam 2 L N) :
    Ward.phiC (Real.sqrt ((1 + 0) / (1 / b))) (H02.z a * H02.z x) =
      (1 - (b : ℂ) • (psibar a * psi a)) * (1 - (b : ℂ) • (psibar x * psi x)) := by
  have hc : Real.sqrt ((1 + 0) / (1 / b)) ^ 2 = b := by
    rw [Real.sq_sqrt (by positivity), onept_b_eq]
  rw [map_mul, Ward.phiC_z, Ward.phiC_z, hc, Ward.psibar_mul_psi' a a,
    Ward.psibar_mul_psi' x x, smul_neg, smul_neg, sub_neg_eq_add, sub_neg_eq_add]

end Model

variable {L N : ℕ} [NeZero L]

/-- **`b⟨ψ̄_0ψ_x⟩ = -⟨z̃_0z̃_x⟩ + p` with `0 ≤ p ≤ r = 1 - b⟨ψ̄_0ψ_0⟩`** (`h ≥ 0`), where
`p = P_{1/b,h}[0 ↔ g, x ↔ g]`. -/
theorem twopt_eq_neg_zz {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq) (hh : b ≤ μ₀ + msq)
    (x : Lam 2 L N) :
    ∃ p r : ℝ, 0 ≤ p ∧ p ≤ r ∧ r ≤ 1 ∧
      1 - (b : ℂ) * avg0 L N msq b μ₀ (psibar 0 * psi 0) = r ∧
      (b : ℂ) * avg0 L N msq b μ₀ (psibar 0 * psi x) =
        -avg0 L N msq b μ₀ ((1 - (b : ℂ) • (psibar 0 * psi 0)) *
          (1 - (b : ℂ) • (psibar x * psi x))) + p := by
  set h := (μ₀ + msq) / b - 1 with hhd
  have hh0 : 0 ≤ h := onept_h_nonneg hb hh
  have hw := Ward.nnW_symm (d := 2) (L := L) (N := N) (1 / b)
  have hw0 := Ward.nnW_nonneg (d := 2) (L := L) (N := N) (β := 1 / b) (by positivity)
  have hV := Vh_eq_V0 (μ₀ := μ₀) (msq := msq) hb
  set gw := H02.ghostW (Ward.nnW 2 L N (1 / b)) (fun _ : Lam 2 L N => h)
  have hgw := H02.ghostW_symm hw (fun _ : Lam 2 L N => h)
  have hgw0 := H02.ghostW_nonneg hw0 (fun _ : Lam 2 L N => hh0)
  set p := H02.arborealProb gw hgw
    (fun F => F.Reachable (some (0 : Lam 2 L N)) none ∧ F.Reachable (some x) none) with hpd
  set r := H02.arborealProb gw hgw (fun F => F.Reachable (some (0 : Lam 2 L N)) none) with hrd
  have hsplit := arborealProb_or_disj hgw
    (fun F => F.Reachable (some (0 : Lam 2 L N)) none ∧ F.Reachable (some x) none)
    (fun F => F.Reachable (some (0 : Lam 2 L N)) none ∧ ¬F.Reachable (some x) none)
    (fun F => F.Reachable (some (0 : Lam 2 L N)) none) (fun F => by tauto) (fun F h => h.2.2 h.1.2)
  have hq := H02.arborealProb_nonneg hgw hgw0
    (fun F => F.Reachable (some (0 : Lam 2 L N)) none ∧ ¬F.Reachable (some x) none)
  have hr1 := H02.arborealProb_le_one hgw hgw0
    (fun F => F.Reachable (some (0 : Lam 2 L N)) none)
  -- `r = ⟨z_0⟩`, `⟨z_0z_x⟩ = p - ⟨ξ_0η_x⟩`
  have hz := H02.arborealProb_ghost_zforest hw hw0 (h := fun _ => h) (fun _ => hh0) 0
  have hzz := avg_zz_split hw hw0 (h := fun _ => h) (fun _ => hh0) 0 x
  have hZ := onept_Zb_ne (L := L) (N := N) hb hm0 hh
  simp only [avg0, V0c] at hZ ⊢
  rw [← hV] at hZ ⊢
  have hpr : r = p + H02.arborealProb gw hgw
      (fun F => F.Reachable (some (0 : Lam 2 L N)) none ∧ ¬F.Reachable (some x) none) := hsplit
  refine ⟨p, r, H02.arborealProb_nonneg hgw hgw0 _, by linarith, hr1, ?_, ?_⟩
  · rw [hrd, hz, Ward.bridge_avg_z (s₀ := 0) (by positivity) (by norm_num) hm0 hZ, onept_b_eq b]
  · have e1 := Ward.bridge_avg (d := 2) (L := L) (N := N) (β := 1 / b) (h := h) (s₀ := 0)
      (by positivity) (by norm_num) hm0 (H02.z 0 * H02.z x)
    have e2 := Ward.bridge_avg_ξη (d := 2) (L := L) (N := N) (β := 1 / b) (h := h) (s₀ := 0)
      (by positivity) (by norm_num) hm0 0 x
    rw [phiC_zz_eq hb] at e1
    rw [onept_b_eq b] at e2
    rw [← e1, ← e2, hzz]
    push_cast
    ring

/-- **Translation invariance of the one-point function**: `⟨ψ̄_xψ_x⟩ = ⟨ψ̄_0ψ_0⟩`. -/
theorem avg0_diag_transl {b μ₀ msq : ℝ} (hm0 : 0 < msq) (hN : 1 ≤ N) (x : Lam 2 L N) :
    avg0 L N msq b μ₀ (psibar x * psi x) = avg0 L N msq b μ₀ (psibar 0 * psi 0) := by
  have := PtCorr.avg_psibar_psi_diag_transl hm0 hN (V0c b μ₀) x (0 : Lam 2 L N)
  rwa [zero_add] at this

end

end PtCorr2
