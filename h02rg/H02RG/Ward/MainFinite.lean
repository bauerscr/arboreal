import Ward.Model

/-!
# Finite-volume identities for the assembly of `thm:h02`

For real `b > 0`, `m² > 0` with `s₀ > -1` and `h(b, m²) ≥ 0`, with `β = β(b, m²)`,
`h = h(b, m²)`, `c² = c2F b m²` and `⟨·⟩ = Obs.avg (Cov) (VE (V₀c m² b) Λ)`:

* `ZM_ne_zero`: `Z_{m², b} ≠ 0` (it is a positive multiple of `Z_{β,h} > 0`);
* `avgH_z`: `⟨z_a⟩_{β,h} = 1 - c² ⟨ψ̄_aψ_a⟩`, `avgH_ξη`: `⟨ξ_aη_x⟩_{β,h} = c² ⟨ψ̄_aψ_x⟩`;
* `avgH_cov`: `⟨z_a z_x⟩ - ⟨z_a⟩⟨z_x⟩ = c⁴ (⟨ψ̄_aψ_a ψ̄_xψ_x⟩ - ⟨ψ̄_aψ_a⟩⟨ψ̄_xψ_x⟩)`;
* `avgH_z_transl`: `⟨z_x⟩ = ⟨z_0⟩`; `avgH_dot`: `⟨u_a·u_x⟩ = -2⟨ξ_aη_x⟩ - ⟨z_a z_x⟩`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4

variable {d L N : ℕ} [NeZero L] {V₀c : ℝ → ℂ → Vcoup}

/-! ### Linearity of the `ℍ^{0|2}` average -/

section Lin

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (w : Λ → Λ → ℝ) (h : Λ → ℝ)

theorem avgH_add (F G : H02.Grassmann Λ) : H02.avg w h (F + G) = H02.avg w h F + H02.avg w h G := by
  simp only [H02.avg, H02.expect_add, add_div]

theorem avgH_sub (F G : H02.Grassmann Λ) : H02.avg w h (F - G) = H02.avg w h F - H02.avg w h G := by
  simp only [H02.avg, H02.expect_sub, sub_div]

theorem avgH_neg (F : H02.Grassmann Λ) : H02.avg w h (-F) = -H02.avg w h F := by
  simp only [H02.avg, H02.expect_neg, neg_div]

theorem avgH_one (hZ : H02.expect w h 1 ≠ 0) : H02.avg w h 1 = 1 := div_self hZ

end Lin

theorem z_mul_z {Λ : Type*} [DecidableEq Λ] (a x : Λ) :
    H02.z a * H02.z x = 1 - H02.ξ a * H02.η a - H02.ξ x * H02.η x +
      H02.ξ a * H02.η a * (H02.ξ x * H02.η x) := by
  unfold H02.z; noncomm_ring

/-! ### The model identities -/

section Model

variable (hconj : ∀ msq b₀, V₀c msq (starRingEnd ℂ b₀) = (V₀c msq b₀).conj)
  (hbb : ∀ msq b₀, (V₀c msq b₀).b = b₀)
  {b m : ℝ} (hb : 0 < b) (hs : -1 < s0R V₀c b m) (hm : 0 < m) (hh : 0 ≤ hF V₀c b m)
include hconj hbb hb hs hm hh

theorem ZM_ne_zero : ZM d L N V₀c m b ≠ 0 := by
  intro h0
  have h1 := expect_one_eq (d := d) (L := L) (N := N) hconj hb hs hm
  rw [h0, mul_zero] at h1
  have h2 := expect_one_pos_nnW (d := d) (L := L) (N := N) (betaF_pos hb hs).le hh
  have : (H02.expect (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) 1 : ℂ) ≠ 0 := by
    exact_mod_cast h2.ne'
  exact this h1

theorem expectH_ne_zero : H02.expect (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) 1 ≠ 0 :=
  (expect_one_pos_nnW (betaF_pos hb hs).le hh).ne'

theorem avgH_ξη (a x : Lam d L N) :
    ((H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.ξ a * H02.η x) : ℝ) : ℂ) =
      (c2F V₀c b m : ℂ) * avg (Suscept.Cov d L N m) (VE (V₀c m b) univ) (psibar a * psi x) := by
  rw [avg_ξη_eq hconj hb hs hm, avgM_eq (hbb m b)]

theorem avgH_z (a : Lam d L N) :
    ((H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.z a) : ℝ) : ℂ) =
      1 - (c2F V₀c b m : ℂ) * avg (Suscept.Cov d L N m) (VE (V₀c m b) univ) (psibar a * psi a) := by
  rw [avg_z_eq hconj hb hs hm (ZM_ne_zero hconj hbb hb hs hm hh), avgM_eq (hbb m b)]

theorem avgH_ξηξη (a x : Lam d L N) :
    ((H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m)
        (H02.ξ a * H02.η a * (H02.ξ x * H02.η x)) : ℝ) : ℂ) =
      (c2F V₀c b m : ℂ) ^ 2 * avg (Suscept.Cov d L N m) (VE (V₀c m b) univ)
        (psibar a * psi a * (psibar x * psi x)) := by
  rw [bridge_avg_ξηξη (betaF_pos hb hs) hs hm, Vh_eq_V₀sp hconj hb hs, c2F_eq hb hs]
  push_cast
  rw [← avgM_eq (hbb m b)]; rfl

theorem avgH_cov (a x : Lam d L N) :
    ((H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.z a * H02.z x) -
        H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.z a) *
          H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.z x) : ℝ) : ℂ) =
      (c2F V₀c b m : ℂ) ^ 2 * (avg (Suscept.Cov d L N m) (VE (V₀c m b) univ)
          (psibar a * psi a * (psibar x * psi x)) -
        avg (Suscept.Cov d L N m) (VE (V₀c m b) univ) (psibar a * psi a) *
          avg (Suscept.Cov d L N m) (VE (V₀c m b) univ) (psibar x * psi x)) := by
  have hZ := expectH_ne_zero (d := d) (L := L) (N := N) hconj hbb hb hs hm hh
  have e1 : H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.z a * H02.z x) =
      1 - H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.ξ a * H02.η a) -
        H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.ξ x * H02.η x) +
        H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m)
          (H02.ξ a * H02.η a * (H02.ξ x * H02.η x)) := by
    rw [z_mul_z, avgH_add, avgH_sub, avgH_sub, avgH_one _ _ hZ]
  have e2 : ∀ y : Lam d L N, H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.z y) =
      1 - H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.ξ y * H02.η y) :=
    fun y => by rw [H02.z, avgH_sub, avgH_one _ _ hZ]
  rw [e1, e2, e2]
  push_cast
  rw [avgH_ξη hconj hbb hb hs hm hh, avgH_ξη hconj hbb hb hs hm hh,
    avgH_ξηξη hconj hbb hb hs hm hh]
  ring

theorem avgH_z_transl (hN : 1 ≤ N) (x : Lam d L N) :
    H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.z x) =
      H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.z 0) := by
  have h1 := avgH_z (N := N) hconj hbb hb hs hm hh x
  have h2 := avgH_z (N := N) hconj hbb hb hs hm hh (0 : Lam d L N)
  have ht := avg_psibar_psi_diag_transl (msq := m) hm hN (V₀c m b) x (0 : Lam d L N)
  rw [zero_add] at ht
  rw [ht, ← h2] at h1
  exact_mod_cast h1

theorem avgH_dot (a x : Lam d L N) :
    H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.dot a x) =
      -2 * H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.ξ a * H02.η x) -
        H02.avg (nnW d L N (betaF V₀c b m)) (fun _ => hF V₀c b m) (H02.z a * H02.z x) := by
  rw [H02.dot, avgH_sub, avgH_sub, avgH_neg, ← avg_ξη_symm_nnW (betaF V₀c b m) (hF V₀c b m) a x]
  ring

end Model

end

end Ward
