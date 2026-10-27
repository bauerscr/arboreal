import Ward.MainAll

/-!
# Main theorems of `h02rg-lean.tex` (the arboreal gas / `H^{0|2}` model in `d ≥ 3`)

The theorem-level results of `h02rg-lean.tex` (Section `sec:lean`), with their labels in
`h02rg-lean.tex` and in the paper `src/h02rg.tex`:

* `H02RG.thm_forest_macro`: `h02rg-lean.tex` Theorem `thm:macro` (= part (A) of `thm:all`);
  `h02rg.tex` Theorem 1.1 `thm:forest-macro`.
* `H02RG.thm_h02`: part (B) of `h02rg-lean.tex` Theorem `thm:all`; `h02rg.tex` Theorem 1.5 `thm:h02`.
* `H02RG.thm_forests0`: part (C) of `h02rg-lean.tex` Theorem `thm:all`; `h02rg.tex` Theorem 1.2
  `thm:forests0` (without `θ_d² = ζ_d`).
* `H02RG.thm_forests`: part (D) of `h02rg-lean.tex` Theorem `thm:all`; `h02rg.tex` Theorem 1.3
  `thm:forests` (without the identities between the constants).
* `H02RG.thm_all`: `h02rg-lean.tex` Theorem `thm:all` (parts (A)–(E) with shared constants).

The statement predicates (`FMBody`, `H02Body`, `F0Body`, `FBody`, `AllBody`) and the proofs for a
given initial coupling (`thm_forest_macro_of`, `thm_h02_of`, `thm_all_of`) stay in
`H02RG/Ward/ForestMacro.lean`, `H02RG/Ward/Main.lean` and `H02RG/Ward/MainAll.lean`.
-/

/-! ### `thm:forest-macro` (from `H02RG/Ward/ForestMacro.lean`) -/

namespace H02RG

noncomputable section

open Ward Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology Metric

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-- **Theorem `thm:forest-macro`** (`h02rg.tex` line 231), with the full quantifier prefix:
`P^{Λ_N}_{β,0}[0 ↔ x] = ζ_d(β) + 𝖼₀(β)/(β|x|^{d-2}) + O(β^{-1}|x|^{-(d-2+κ)}) + O(β^{-1}L^{-κN})`,
`ζ_d(β) = 1 + O(1/β)`, `𝖼₀(β) = 𝖼₀ + O(1/β)`, `𝖼₀ > 0` (`N ≥ 2`, `x ≠ 0`). -/
theorem thm_forest_macro (hd : 3 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ (β₀ κ' Cf c0 : ℝ) (ζ c₀ : ℝ → ℝ), 0 < β₀ ∧ 0 < κ' ∧ κ' ≤ 1 ∧ 0 ≤ Cf ∧ 0 < c0 ∧
      ∀ β, β₀ ≤ β → |ζ β - 1| ≤ Cf / β ∧ |c₀ β - c0| ≤ Cf / β ∧
      ∀ N : ℕ, 2 ≤ N → ∀ x : Lam d L N, x ≠ 0 →
        |H02.arborealProb (nnW d L N β) (nnW_symm _) (fun F => F.Reachable 0 x) - ζ β -
            c₀ β / (β * Ward.eNorm (rep x) ^ ((d : ℝ) - 2))| ≤
          Cf / β * Ward.eNorm (rep x) ^ (-((d : ℝ) - 2 + κ')) + Cf / β * (L : ℝ) ^ (-(κ' * N)) := by
  obtain ⟨L₀, H⟩ := exists_flowDataW hd
  exact ⟨L₀, fun L _ hL hLodd => by
    obtain ⟨A, ℓ₀, V₀c, lbar, C, κ, HW⟩ := H L hL hLodd
    exact thm_forest_macro_of hd HW hLodd⟩

end

end H02RG

/-! ### `thm:h02`, `thm:forests0`, `thm:forests` (from `H02RG/Ward/Main.lean`) -/

namespace H02RG

noncomputable section

open Ward Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Metric Filter Topology FRD.GreenAsymp

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-- **Theorem `thm:h02`** (h02rg.tex, line 511). -/
theorem thm_h02 (hd : 3 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ (β₀ κ' K : ℝ) (θ c₁ c₂ : ℝ → ℝ), 0 < β₀ ∧ 0 < κ' ∧ 0 ≤ K ∧
      ∀ β, β₀ ≤ β → H02Body d L κ' K θ c₁ c₂ β := by
  obtain ⟨L₀, H⟩ := exists_flowDataW hd
  refine ⟨L₀, fun L _ hL hLodd => ?_⟩
  obtain ⟨A, ℓ₀, V₀c, lbar, C, κ, HW⟩ := H L hL hLodd
  exact thm_h02_of hd HW hLodd

/-- **Theorem `thm:forests0`** (h02rg.tex, line 316), without the identity `θ_d² = ζ_d`:
the limit `θ_d(β) = lim_{h↓0} lim_N P_{β,h}[0 ↔ g]` exists and `θ_d(β) = 1 + O(1/β)`. -/
theorem thm_forests0 (hd : 3 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ (β₀ K : ℝ) (θ : ℝ → ℝ), 0 < β₀ ∧ ∀ β, β₀ ≤ β → |θ β - 1| ≤ K / β ∧
      ∃ θh' : ℝ → ℝ, (∀ h, 0 < h → Tendsto (fun N =>
          H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
            (H02.ghostW_symm (nnW_symm β) _) (fun F => F.Reachable (some (0 : Lam d L N)) none))
          atTop (𝓝 (θh' h))) ∧ Tendsto θh' (𝓝[>] 0) (𝓝 (θ β)) := by
  obtain ⟨L₀, H⟩ := thm_h02 hd
  refine ⟨L₀, fun L _ hL hLodd => ?_⟩
  obtain ⟨β₀, κ', K, θ, c₁, c₂, hβ₀, -, -, Hb⟩ := H L hL hLodd
  refine ⟨β₀, K, θ, hβ₀, fun β hβ => ?_⟩
  obtain ⟨h1, -, -, -, ⟨θh', hlim, hcont⟩, -⟩ := Hb β hβ
  have hβ0 : 0 ≤ β := by linarith
  refine ⟨h1, θh', fun h hh => ?_, hcont⟩
  refine (hlim h hh).congr fun N => ?_
  exact (Pg_eq hβ0 hh.le).symm

/-- **Theorem `thm:forests`** (h02rg.tex, line 353), without the identities between the
constants: with `c₁, c₂` of `thm_h02`,
`τ_β(x) = lim_{h↓0} lim_N P[0 ↔ x, 0 ↮ g] = c₁/(β|x|^{d-2}) + O(1/(β|x|^{d-2+κ}))` and
`σ_β(x) = lim_{h↓0} lim_N (P[0 ↮ g]² - P[0 ↮ x, 0 ↮ g, x ↮ g]) = c₂/(β²|x|^{2d-4}) +
O(1/(β²|x|^{2d-4+κ}))`. -/
theorem thm_forests (hd : 3 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ (β₀ κ' K : ℝ) (c₁ c₂ : ℝ → ℝ), 0 < β₀ ∧ 0 < κ' ∧
      ∀ β, β₀ ≤ β → |c₁ β - cd d| ≤ K / β ∧ |c₂ β - cd d ^ 2| ≤ K / β ∧
      ∀ x : Zd d, x ≠ 0 →
        (∃ (τh' : ℝ → ℝ) (τ₀ : ℝ),
          (∀ h, 0 < h → Tendsto (fun N =>
            H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
              (H02.ghostW_symm (nnW_symm β) _) (fun F => (H02.base F).Reachable (0 : Lam d L N)
                (toT L N x) ∧ ¬F.Reachable (some (0 : Lam d L N)) none)) atTop (𝓝 (τh' h))) ∧
          Tendsto τh' (𝓝[>] 0) (𝓝 τ₀) ∧
          |τ₀ - c₁ β * Ward.eNorm x ^ (-((d : ℝ) - 2)) / β| ≤
            K * Ward.eNorm x ^ (-((d : ℝ) - 2 + κ')) / β) ∧
        (∃ (σh' : ℝ → ℝ) (σ₀ : ℝ),
          (∀ h, 0 < h → Tendsto (fun N =>
            H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
                (H02.ghostW_symm (nnW_symm β) _)
                (fun F => ¬F.Reachable (some (0 : Lam d L N)) none) ^ 2 -
              H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
                (H02.ghostW_symm (nnW_symm β) _) (fun F =>
                  ¬F.Reachable (some (0 : Lam d L N)) none ∧
                    ¬F.Reachable (some (toT L N x)) none ∧
                    ¬F.Reachable (some (0 : Lam d L N)) (some (toT L N x)))) atTop
            (𝓝 (σh' h))) ∧
          Tendsto σh' (𝓝[>] 0) (𝓝 σ₀) ∧
          |σ₀ - c₂ β * Ward.eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2| ≤
            K * Ward.eNorm x ^ (-(2 * ((d : ℝ) - 2) + κ')) / β ^ 2) := by
  obtain ⟨L₀, H⟩ := thm_h02 hd
  refine ⟨L₀, fun L _ hL hLodd => ?_⟩
  obtain ⟨β₀, κ', K, θ, c₁, c₂, hβ₀, hκ', -, Hb⟩ := H L hL hLodd
  refine ⟨β₀, κ', K, c₁, c₂, hβ₀, hκ', fun β hβ => ?_⟩
  obtain ⟨-, h2, h3, htr, -, hτ, hσ, -⟩ := Hb β hβ
  have hβ0 : 0 ≤ β := by linarith
  refine ⟨h2, h3, fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨τh', τ₀, hlim, hcont, hest⟩ := hτ x hx
    refine ⟨τh', τ₀, fun h hh => (hlim h hh).congr fun N => ?_, hcont, hest⟩
    exact ((H02.prop_h02_forest (nnW_symm β) (nnW_nonneg hβ0) h hh.le 0 (toT L N x)).2.1).symm
  · obtain ⟨σh', σ₀, hlim, hcont, hest⟩ := hσ x hx
    refine ⟨fun h => -σh' h, -σ₀, fun h hh => ?_, hcont.neg, ?_⟩
    · refine (hlim h hh).neg.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      obtain ⟨hz, -, -, -, hsig⟩ :=
        H02.prop_h02_forest (nnW_symm β) (nnW_nonneg hβ0) h hh.le (0 : Lam d L N) (toT L N x)
      obtain ⟨hzx, -⟩ :=
        H02.prop_h02_forest (nnW_symm β) (nnW_nonneg hβ0) h hh.le (toT L N x) (toT L N x)
      have hn := fun (a : Lam d L N) => H02.arborealProb_not
        (H02.ghostW_symm (nnW_symm β) (fun _ => h)) (H02.ghostW_nonneg (nnW_nonneg hβ0)
          (fun _ => hh.le)) (fun F => F.Reachable (some a) none)
      have hPx : H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
            (H02.ghostW_symm (nnW_symm β) _) (fun F => ¬F.Reachable (some (toT L N x)) none) =
          H02.arborealProb (H02.ghostW (nnW d L N β) (fun _ => h))
            (H02.ghostW_symm (nnW_symm β) _) (fun F => ¬F.Reachable (some (0 : Lam d L N)) none) := by
        rw [hn, hn, hzx, hz, htr h hh N hN]
      rw [hsig, hPx]
      ring
    · rw [show -σ₀ - c₂ β * Ward.eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2 =
        -(σ₀ + c₂ β * Ward.eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2) by ring, abs_neg]
      exact hest

end

end H02RG

/-! ### `thm:all` (from `H02RG/Ward/MainAll.lean`) -/

namespace H02RG

noncomputable section

open Ward Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology Metric FRD.GreenAsymp

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-- **`thm:forest-macro`, `thm:h02`, `thm:forests0`, `thm:forests`** (h02rg.tex lines 231, 511,
316, 353) with shared constants `ζ, c₀, θ, c₁, c₂` for one initial coupling, and the identities
`θ² = ζ`, `c₂θ²/c₁² = 1`, `c₀ = 2c₁`; `𝖼₀ = 2c_d`, `c₁ = c_d + O(1/β)`, `c₂ = c_d² + O(1/β)`. -/
theorem thm_all (hd : 3 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ (β₀ κ' K Cf c0 : ℝ) (ζ c₀ θ c₁ c₂ : ℝ → ℝ), 0 < β₀ ∧ 0 < κ' ∧ κ' ≤ 1 ∧ 0 ≤ K ∧
      0 ≤ Cf ∧ c0 = 2 * cd d ∧ 0 < c0 ∧
      ∀ β, β₀ ≤ β → AllBody d L κ' K Cf c0 ζ c₀ θ c₁ c₂ β := by
  obtain ⟨L₀, H⟩ := exists_flowDataW hd
  refine ⟨L₀, fun L _ hL hLodd => ?_⟩
  obtain ⟨A, ℓ₀, V₀c, lbar, C, κ, HW⟩ := H L hL hLodd
  exact thm_all_of hd HW hLodd

end

end H02RG
