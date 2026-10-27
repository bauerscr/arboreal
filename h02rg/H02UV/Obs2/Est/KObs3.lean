import Obs2.Est.Step2O
import Obs2.Est.KObs2

/-!
# The `K^{obs}` step for `K_{j+1} - K^{(2)}`: `kobs_step` with `hK'` discharged

`kobs_step` (`Obs2/Est/KObs2.lean`) assumes the bound `hK'` in the `λ`-norm, `λ = ḡ/m`. That bound has
no `ḡ²` term, so it can only hold for `K_{j+1} - K^{(2)}` (the second-order part `K^{(2)}` is
reapportioned by the change of variables). **`kobs2_step`** proves the conclusion of `kobs_step`
for `F = K_{j+1}(U) - K^{(2)}(U)` (weighted by `A^{(|𝓑_{j+1}(U)| - 2^d)_+}`): `step2O_ts` in the
rescaled weights `Wt.scale λ w` provides `hK'` (with `ḡ³ ≤ (2ḡ)³`), and `lam_trick` concludes.

With `θ₀ = C₀ (L^{d-3} + A^{-η})`, observable sizes `‖V^{obs}‖ ≤ m`, `‖𝒲^{obs}‖ ≤ ḡ m`,
`‖K^∅‖ ≤ c_b ḡ³`, `‖K^{obs}‖ ≤ c_k ḡ² m`:
`A^{(|𝓑_{j+1}(U)| - 2^d)_+} ‖(K_{j+1}(U) - K^{(2)}(U))^{obs}‖ ≤ (θ₀ + C₁(2 + 2c_b + c_k)ḡ) k
  + (θ₀ c_b + C₁(8 + 2c_b + c_b²)) ḡ² m`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

theorem oTo_scale {w : Wt} (hw0 : w.ab = 0) (lam : ℝ≥0∞) (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) :
    oTo (Wt.scale lam w) j ℓ F = lam * oTo w j ℓ F := by
  rw [oTo_eq_ab (by simp [Wt.scale, hw0]), oTo_eq_ab hw0]
  simp only [Wt.scale]
  ring

set_option maxHeartbeats 1000000 in
/-- **The `K^{obs}` step for `K_{j+1} - K^{(2)}`** (`kobs_step` with `hK'` proved). -/
theorem kobs2_step (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.ab = 0 → w.a ≠ ⊤ → w.b ≠ ⊤ →
    ∀ (V W : OFam c d L N) (K : OAct c d L N),
      InF j (bulkF V) → InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam d L N)) : Alg d L N) = 0) → InK2 j (bulkF K) →
      (∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (V b : SA c (Lam d L N))) →
      (∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (W b : SA c (Lam d L N))) →
      (∀ X, IsConn j X → CmpIn (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N))) →
      (∀ X, IsConn j X → IsSymS (K X : SA c (Lam d L N))) →
      (∀ X, IsConn j X → P.a ∉ nbhd j X → (K X : SA c (Lam d L N)).a = 0) →
      (∀ X, IsConn j X → P.b ∉ nbhd j X → (K X : SA c (Lam d L N)).b = 0) →
      ∀ g m b k cb ck : ℝ, 0 < g → g ≤ 1 → g ≤ ε₀ → 0 < m → 0 ≤ b → b ≤ cb * g ^ 3 → 0 ≤ cb →
      0 ≤ k → k ≤ ck * g ^ 2 * m → 0 ≤ ck → b + g / m * k ≤ ε₀ →
      Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal g → Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal (g ^ 2) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal m) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal (g * m)) →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal b →
      (∀ X, IsConn j X →
        ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ ENNReal.ofReal k) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal (A ^ (nb (j + 1) U - 2 ^ d)) *
          oTo w (j + 1) ℓ' (Knext2O P j C V W K U - K2O j C V U) ≤
          ENNReal.ofReal ((C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) +
              C₁ * (2 + 2 * cb + ck) * g) * k +
            (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) * cb + C₁ * (8 + 2 * cb + cb ^ 2)) *
              g ^ 2 * m) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := step2O_ts d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε₀, hC₁, h⟩ := h A hA
  refine ⟨ε₀, C₁, hε₀, hC₁, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw0 hwa hwb V W K hV hW hV0 hK hlocV hlocW
    hlocK hsym hza hzb g m b k cb ck hg hg1 hgε hm hb0 hb hcb hk0 hkk hck hkε hVg hWg hVo hWo hKb
    hKo U hU
  have hA0 : 0 < A := by linarith
  set l := g / m with hl
  have hl0 : 0 < l := div_pos hg hm
  have hlm : l * m = g := by rw [hl, div_mul_cancel₀ g hm.ne']
  set wl := Wt.scale (ENNReal.ofReal l) w with hwl
  have hwl0 : wl.ab = 0 := by simp [hwl, Wt.scale, hw0]
  have hwla : wl.a ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwa
  have hwlb : wl.b ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwb
  set kt := b + l * k with hkt
  have hkt0 : 0 ≤ kt := by positivity
  have hlk : l * k ≤ kt := le_add_of_nonneg_left hb0
  have H := h N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P wl hwl0 hwla hwlb V W K hV hW hV0 hK
    hlocV hlocW hlocK hsym hza hzb g hg.le hgε hVg hWg
    (fun b' hb' => by
      rw [oTo_scale hw0, ← hlm, ENNReal.ofReal_mul hl0.le]
      exact mul_le_mul_left' (hVo b' hb') _)
    (fun b' hb' => by
      rw [oTo_scale hw0, show g ^ 2 = l * (g * m) by rw [pow_two, ← hlm]; ring,
        ENNReal.ofReal_mul hl0.le]
      exact mul_le_mul_left' (hWo b' hb') _)
    kt hkt0 hkε (hKb.trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity))))
    (fun X hX => by
      rw [oTo_scale hw0, mul_left_comm]
      refine (mul_le_mul_left' (hKo X hX) _).trans ?_
      rw [← ENNReal.ofReal_mul hl0.le]
      exact ENNReal.ofReal_le_ofReal hlk)
    U hU
  set θ₀ := C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) with hθ
  have hθ0 : 0 ≤ θ₀ := by positivity
  set wt : ℝ := A ^ (nb (j + 1) U - 2 ^ d)
  have hwt0 : 0 ≤ wt := pow_nonneg hA0.le _
  set F := Knext2O P j C V W K U - K2O j C V U
  set X := ENNReal.ofReal wt * oTo w (j + 1) ℓ' F
  set Rr := θ₀ * kt + C₁ * ((2 * g) ^ 3 + 2 * g * kt + kt ^ 2) with hRr
  have hR0 : 0 ≤ Rr := by positivity
  have h1 : ENNReal.ofReal l * X ≤ ENNReal.ofReal Rr := by
    rw [oTj_scale hw0] at H
    have hg3 : g ^ 3 ≤ (2 * g) ^ 3 := pow_le_pow_left₀ hg.le (by linarith) 3
    have hgk : g * kt ≤ 2 * g * kt := by nlinarith
    calc ENNReal.ofReal l * X = ENNReal.ofReal wt * (ENNReal.ofReal l * oTo w (j + 1) ℓ' F) := by
          simp only [X]; ring
      _ ≤ ENNReal.ofReal wt * (Tj d (L : ℝ) (j + 1) ℓ' (F : SA c (Lam d L N)).e +
            ENNReal.ofReal l * oTo w (j + 1) ℓ' F) := mul_le_mul_left' le_add_self _
      _ ≤ _ := H
      _ = ENNReal.ofReal (θ₀ * kt + C₁ * (g ^ 3 + g * kt + kt ^ 2)) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal Rr := by
          refine ENNReal.ofReal_le_ofReal (add_le_add le_rfl ?_)
          refine mul_le_mul_of_nonneg_left ?_ hC₁
          linarith
  have hfin : X ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simpa using hl0)] at h1
    exact ENNReal.ofReal_ne_top (top_le_iff.1 h1)
  have h2 : g / m * X.toReal ≤ Rr := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hl0.le, ENNReal.toReal_ofReal hR0] at this
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal
    (lam_trick hm hg hg1 hk0 hθ0 hC₁ hb0 hb hcb hkk hck h2)

end

end Obs2
