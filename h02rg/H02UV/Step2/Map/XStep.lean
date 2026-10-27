import Step2.Map.Spaces2

/-!
# The irrelevant coordinates in raw fields (`h02uv-outline.tex`, Section `sec:reduction`, (O1))

In raw fields (route (O5), no rescaling) the remainder coordinate `D = W - W^lin` evolves by
`D_{j+1} = T_j D_j + R_j(V_j, W^lin_j + D_j)` (`Dnext_eq`), where `W^lin_{j+1} = Src_j(V,V) + T_j W^lin_j`.
Hence (`Dnext_bound`) `‖D_{j+1}‖ ≤ C₀L^{d-3}‖D_j‖ + C₃(v² + w)²` with `w ≥ ‖W^lin_j + D_j‖`: the
(Yb) bound of `Flow2.Hist.RGBound`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- `W^lin_{j+1} = Src_j(V, V) + T_j W^lin_j` in raw fields. -/
def WlinNext (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V Wl : Fam d L N) : Fam d L N :=
  SrcL j C (EthEL C) V V + TrL j C 1 Wl

/-- The remainder coordinate after one step. -/
def Dnext (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V Wl D : Fam d L N) : Fam d L N :=
  fun c => Wnext2 j C V (Wl + D) c - WlinNext j C V Wl c

/-- **`D_{j+1} = T_j D_j + R_j(V, W^lin + D)`.** -/
theorem Dnext_eq (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V Wl D : Fam d L N) :
    Dnext j C V Wl D = TrL j C 1 D + fun c => RemW j C V (Wl + D) c := by
  funext c
  simp only [Dnext, WlinNext, Pi.add_apply, Wnext2_decomp, map_add]
  abel

/-- **The (Yb) bound**: `‖D_{j+1}‖ ≤ C₀L^{d-3}‖D‖ + C₃(v² + w)²`. -/
theorem Dnext_bound_ts (d : ℕ) (hd : 2 ≤ d) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₃ : ℝ, 0 ≤ C₃ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ → ℓC ≤ ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C → TInv C →
    ∀ V Wl D : Fam d L N, InF j V → InF j Wl → InF j D → FamCovG j D →
    (∀ b, ε (V b : Alg d L N) = 0) →
    ∀ v w δ : ℝ, 0 ≤ v → 0 ≤ w → 0 ≤ δ → v ≤ 1 → w ≤ 1 →
    Fnorm j ℓ V ≤ ENNReal.ofReal v → Fnorm j ℓ (Wl + D) ≤ ENNReal.ofReal w →
    Fnorm j ℓ D ≤ ENNReal.ofReal δ →
      Fnorm (j + 1) ℓ' (Dnext j C V Wl D) ≤
        ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3) * δ + C₃ * (v ^ 2 + w) ^ 2) := by
  obtain ⟨C₀, hC₀, L₁, hT⟩ := TrL_contract'_ts d hd
  obtain ⟨L₂, hP⟩ := prodRem_bound_ts d (by omega)
  refine ⟨C₀, hC₀, max L₁ L₂, fun L _ hL => ?_⟩
  obtain ⟨C₃, hC₃, hP⟩ := hP L ((le_max_right _ _).trans hL)
  refine ⟨C₃, hC₃, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC hCt V Wl D hV hWl hD hDc hV0 v w δ hv hw hδ hv1 hw1 hVv hWw hDδ
  rw [Dnext_eq]
  refine Fnorm_add_le _ _ (by positivity) (by positivity)
    (hT L ((le_max_left _ _).trans hL) N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum hCℓ C hC hCt D hD hDc 1 (by simp) δ hδ hDδ)
    (iSup₂_le fun c hc => ?_)
  exact hP N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V (Wl + D) hV (inF_add hWl hD) hV0 v w hv hw hv1 hw1 hVv hWw c hc

end

end Step2
