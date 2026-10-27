import Obs2.Est.KObs4W
import Obs2.Est.StepKOWAB

/-!
# The `K^{obs}` step on the `σ_aσ_b` sector (`ab` copy of `Obs2.Est.KObs4W`)

**`kobsK_stepWAB`**: `Obs2.kobsK_stepW` for inputs in `abSub`, `K(X)` anchored, `OLocS`,
`U(1)` invariance, finite weights with `w.Sub`: with input regulator `A`, output regulator `μA`,
`‖V^{obs}‖ ≤ m`, `‖𝒲^{obs}‖ ≤ ḡm`, `A^{(|𝓑_j(X)|-2^d)_+}‖K^{obs}(X)‖ ≤ k`,

  `(μA)^{(|𝓑_{j+1}(U)|-2^d)_+} ‖K^{obs}_{j+1}(U)‖ ≤ (θ₀ + C₁(2+2c_b+c_k)ḡ) k
    + (θ₀ c_b + C₁(8+2c_b+c_b²)) ḡ² m`,  `θ₀ = C₀(L^{d-3} + A^{-η})`.

Proof as `kobsK_stepW`, the observable weight rescaled by `λ = (ḡ/m)^{1/2}`: on `abSub`
`‖π_{obs}F‖_{w_λ} = λ²‖π_{obs}F‖_w = (ḡ/m)‖π_{obs}F‖_w` (`oTo_scaleAB`, `oTj_scaleAB`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

local notation "AB" => (abSub : Subalgebra ℂ (OE c (Lam d L N)))

/-- **The rescaled norm on `abSub`**: `‖π_{obs}F‖_{w_λ} = λ²‖π_{obs}F‖_w`. -/
theorem oTo_scaleAB {w : Wt} (lam : ℝ≥0∞) (j : ℕ) (ℓ : ℝ) {F : OE c (Lam d L N)} (hF : F ∈ AB) :
    oTo (Wt.scale lam w) j ℓ F = lam ^ 2 * oTo w j ℓ F := by
  rw [oTo_of_ab _ _ _ hF, oTo_of_ab _ _ _ hF]
  simp only [Wt.scale]
  ring

theorem oTj_scaleAB {w : Wt} (lam : ℝ≥0∞) (j : ℕ) (ℓ : ℝ) {F : OE c (Lam d L N)} (hF : F ∈ AB) :
    oTj d L (Wt.scale lam w) j ℓ (F : SA c (Lam d L N)) =
      Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).e + lam ^ 2 * oTo w j ℓ F := by
  rw [oTj_eq_bulk_add, oTo_scaleAB lam j ℓ hF]

theorem ofReal_sqrt_sq {l : ℝ} (hl : 0 ≤ l) : ENNReal.ofReal (Real.sqrt l) ^ 2 = ENNReal.ofReal l := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg l), Real.sq_sqrt hl]

set_option maxHeartbeats 1000000 in
/-- **The `K^{obs}` step for the activity after the change of variables** (`K_{j+1} = KplusO`). -/
theorem kobsK_stepWAB (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ μ : ℝ, 1 ≤ μ → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.Sub → w.a ≠ ⊤ → w.b ≠ ⊤ → w.ab ≠ ⊤ →
    ∀ (V W : OFam c d L N) (K : OAct c d L N),
      (∀ b, V b ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ b, W b ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ X, IsConn j X → K X ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ X, IsConn j X → K X ∈ (anc P X : Subalgebra ℂ (OE c (Lam d L N)))) →
      InF j (bulkF V) → InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam d L N)) : Alg d L N) = 0) → InK2 j (bulkF K) →
      OLocS P j V W K →
      (∀ X, IsConn j X → IsSymS (K X : SA c (Lam d L N))) →
      ∀ g m b k cb ck : ℝ, 0 < g → g ≤ 1 → g ≤ ε₀ → 0 < m → 0 ≤ b → b ≤ cb * g ^ 3 → 0 ≤ cb →
      0 ≤ k → k ≤ ck * g ^ 2 * m → 0 ≤ ck → b + g / m * k ≤ ε₀ →
      Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal g → Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal (g ^ 2) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal m) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal (g * m)) →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal b →
      (∀ X, IsConn j X →
        ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ ENNReal.ofReal k) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal ((μ * A) ^ (nb (j + 1) U - 2 ^ d)) *
          oTo w (j + 1) ℓ' (KplusO P j C V W K U) ≤
          ENNReal.ofReal ((C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) +
              C₁ * (2 + 2 * cb + ck) * g) * k +
            (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) * cb + C₁ * (8 + 2 * cb + cb ^ 2)) *
              g ^ 2 * m) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := stepKO_tsWAB d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL μ hμ => ?_⟩
  obtain ⟨A₀, hA₀, h⟩ := h L hL μ hμ
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε₀, hC₁, h⟩ := h A hA
  refine ⟨ε₀, C₁, hε₀, hC₁, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw hwa hwb hwab V W K hVab hWab hKab hKanc hV hW hV0 hK HL
    hsym g m b k cb ck hg hg1 hgε hm hb0 hb hcb hk0 hkk hck hkε hVg hWg hVo hWo hKb
    hKo U hU
  have hA0 : 0 < A := by linarith
  set l := g / m with hl
  have hl0 : 0 < l := div_pos hg hm
  have hlm : l * m = g := by rw [hl, div_mul_cancel₀ g hm.ne']
  set wl := Wt.scale (ENNReal.ofReal (Real.sqrt l)) w with hwl
  have hwl0 : wl.Sub := Wt.scale_sub hw _
  have hwlab : wl.ab ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hwab
  have hsq := ofReal_sqrt_sq hl0.le
  have hwla : wl.a ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwa
  have hwlb : wl.b ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwb
  set kt := b + l * k with hkt
  have hkt0 : 0 ≤ kt := by positivity
  have hlk : l * k ≤ kt := le_add_of_nonneg_left hb0
  have H := h N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P wl hwl0 hwla hwlb hwlab V W K hVab hWab hKab hKanc hV hW hV0 hK
    HL hsym g hg.le hgε hVg hWg
    (fun b' hb' => by
      rw [oTo_scaleAB _ _ _ (hVab b'), hsq, ← hlm, ENNReal.ofReal_mul hl0.le]
      exact mul_le_mul_left' (hVo b' hb') _)
    (fun b' hb' => by
      rw [oTo_scaleAB _ _ _ (hWab b'), hsq, show g ^ 2 = l * (g * m) by rw [pow_two, ← hlm]; ring,
        ENNReal.ofReal_mul hl0.le]
      exact mul_le_mul_left' (hWo b' hb') _)
    kt hkt0 hkε (hKb.trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity))))
    (fun X hX => by
      rw [oTo_scaleAB _ _ _ (hKab X hX), hsq, mul_left_comm]
      refine (mul_le_mul_left' (hKo X hX) _).trans ?_
      rw [← ENNReal.ofReal_mul hl0.le]
      exact ENNReal.ofReal_le_ofReal hlk)
    U hU
  set θ₀ := C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) with hθ
  have hθ0 : 0 ≤ θ₀ := by positivity
  set wt : ℝ := (μ * A) ^ (nb (j + 1) U - 2 ^ d)
  have hwt0 : 0 ≤ wt := pow_nonneg (mul_pos (by linarith) hA0).le _
  set F := KplusO P j C V W K U
  set X := ENNReal.ofReal wt * oTo w (j + 1) ℓ' F
  set Rr := θ₀ * kt + C₁ * ((2 * g) ^ 3 + 2 * g * kt + kt ^ 2) with hRr
  have hR0 : 0 ≤ Rr := by positivity
  have h1 : ENNReal.ofReal l * X ≤ ENNReal.ofReal Rr := by
    rw [oTj_scaleAB _ _ _ ((OAbS.mk hVab hWab hKab).Kplus_ab (P := P) (C := C) U), hsq] at H
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
