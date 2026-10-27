import Obs2.Est.KObsAB

/-!
# The `ab` `K^{obs}` step without the `ḡ²` a priori condition (the linear regime)

On `abSub` the observable sector is *linear* in the `ab` data given the bulk (`σ_aσ_b` squares to
zero). In `kobsK_stepWAB` the quadratic term of the step bound, `C₁k_t²` with `k_t = b + λ²k`,
`λ² = ḡ/m`, contributes `C₁λ²k² = C₁(ḡ/m)k²` to the `ab` activity. It is linear in `k` with a
small coefficient as soon as `k ≤ c_k m`: `C₁(ḡ/m)k² ≤ C₁c_kḡk`. So the a priori condition
`k ≤ c_kḡ²m` of `kobsK_stepWAB` (which a seed of size `O(m)`, or a remainder of size `O(ḡm)`,
violates) can be replaced by `k ≤ c_km`, with the **same** conclusion:

* `lam_trickL`: the real inequality (copy of `lam_trick`, only the bound `λk ≤ c_kḡ` changes);
* **`kobsK_stepWABL`**: `kobsK_stepWAB` with `k ≤ c_k m` in place of `k ≤ c_k ḡ² m`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- The real inequality of the `K` step, linear regime `k ≤ c_k m`. -/
theorem lam_trickL {k k' b m g θ₀ C₁ cb ck : ℝ} (hm : 0 < m) (hg : 0 < g) (hg1 : g ≤ 1)
    (hk : 0 ≤ k) (hθ : 0 ≤ θ₀) (hC : 0 ≤ C₁) (hb0 : 0 ≤ b) (hb : b ≤ cb * g ^ 3) (hcb : 0 ≤ cb)
    (hkk : k ≤ ck * m) (hck : 0 ≤ ck)
    (h : g / m * k' ≤ θ₀ * (b + g / m * k) +
      C₁ * ((2 * g) ^ 3 + 2 * g * (b + g / m * k) + (b + g / m * k) ^ 2)) :
    k' ≤ (θ₀ + C₁ * (2 + 2 * cb + ck) * g) * k + (θ₀ * cb + C₁ * (8 + 2 * cb + cb ^ 2)) * g ^ 2 * m := by
  set l := g / m with hl
  have hl0 : 0 < l := div_pos hg hm
  have hlm : l * m = g := by rw [hl, div_mul_cancel₀ g hm.ne']
  have hg2 : g ^ 2 ≤ 1 := by nlinarith
  have hg3 : g ^ 3 ≤ g ^ 2 := by nlinarith
  have hg3' : g ^ 3 ≤ g := by nlinarith
  -- the pieces, each `≤ l * (⋯)`
  have e1 : θ₀ * b ≤ l * (θ₀ * cb * g ^ 2 * m) := by
    have : l * (θ₀ * cb * g ^ 2 * m) = θ₀ * (cb * g ^ 2 * (l * m)) := by ring
    rw [this, hlm, show cb * g ^ 2 * g = cb * g ^ 3 by ring]
    exact mul_le_mul_of_nonneg_left hb hθ
  have e2 : C₁ * (2 * g) ^ 3 = l * (C₁ * 8 * g ^ 2 * m) := by
    have : l * (C₁ * 8 * g ^ 2 * m) = C₁ * 8 * g ^ 2 * (l * m) := by ring
    rw [this, hlm]; ring
  have hb' : b ≤ cb * g := hb.trans (mul_le_mul_of_nonneg_left hg3' hcb)
  have e3 : C₁ * (2 * g * b) ≤ l * (C₁ * 2 * cb * g ^ 2 * m) := by
    have : l * (C₁ * 2 * cb * g ^ 2 * m) = C₁ * 2 * cb * g ^ 2 * (l * m) := by ring
    rw [this, hlm]
    have hgb : g * b ≤ cb * g ^ 3 := by
      calc g * b ≤ g * (cb * g ^ 3) := mul_le_mul_of_nonneg_left hb hg.le
        _ = cb * g ^ 3 * g := by ring
        _ ≤ cb * g ^ 3 * 1 := mul_le_mul_of_nonneg_left hg1 (by positivity)
        _ = cb * g ^ 3 := by ring
    calc C₁ * (2 * g * b) = C₁ * 2 * (g * b) := by ring
      _ ≤ C₁ * 2 * (cb * g ^ 3) := mul_le_mul_of_nonneg_left hgb (by positivity)
      _ = C₁ * 2 * cb * g ^ 2 * g := by ring
  have e4 : C₁ * b ^ 2 ≤ l * (C₁ * cb ^ 2 * g ^ 2 * m) := by
    have : l * (C₁ * cb ^ 2 * g ^ 2 * m) = C₁ * (cb ^ 2 * g ^ 2 * (l * m)) := by ring
    rw [this, hlm]
    have hb2 : b ^ 2 ≤ (cb * g ^ 3) ^ 2 := pow_le_pow_left₀ hb0 hb 2
    have h3 : g ^ 3 ≤ 1 := hg3'.trans hg1
    have h4 : (cb * g ^ 3) ^ 2 ≤ cb ^ 2 * g ^ 2 * g := by
      rw [show (cb * g ^ 3) ^ 2 = cb ^ 2 * g ^ 2 * g * g ^ 3 by ring]
      exact mul_le_of_le_one_right (by positivity) h3
    exact mul_le_mul_of_nonneg_left (hb2.trans h4) hC
  have e5 : C₁ * (2 * b * (l * k)) ≤ l * (C₁ * 2 * cb * g * k) := by
    have : C₁ * (2 * b * (l * k)) = l * (C₁ * 2 * b * k) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hl0.le
    calc C₁ * 2 * b * k = (C₁ * 2 * k) * b := by ring
      _ ≤ (C₁ * 2 * k) * (cb * g) := mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = C₁ * 2 * cb * g * k := by ring
  have e6 : C₁ * (l * k) ^ 2 ≤ l * (C₁ * ck * g * k) := by
    have : C₁ * (l * k) ^ 2 = l * (C₁ * (l * k) * k) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hl0.le
    have hlk : l * k ≤ ck * g := by
      have h1 : l * k ≤ l * (ck * m) := mul_le_mul_of_nonneg_left hkk hl0.le
      have e : l * (ck * m) = ck * g := by
        rw [show l * (ck * m) = ck * (l * m) by ring, hlm]
      rw [e] at h1
      exact h1
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlk hC) hk
    calc C₁ * (l * k) * k ≤ C₁ * (ck * g) * k := this
      _ = C₁ * ck * g * k := by ring
  have key : g / m * k' ≤ l * ((θ₀ + C₁ * (2 + 2 * cb + ck) * g) * k +
      (θ₀ * cb + C₁ * (8 + 2 * cb + cb ^ 2)) * g ^ 2 * m) := by
    refine h.trans ?_
    have hexp : θ₀ * (b + l * k) + C₁ * ((2 * g) ^ 3 + 2 * g * (b + l * k) + (b + l * k) ^ 2) =
        θ₀ * b + l * (θ₀ * k) + C₁ * (2 * g) ^ 3 + C₁ * (2 * g * b) + l * (C₁ * 2 * g * k) +
          C₁ * b ^ 2 + C₁ * (2 * b * (l * k)) + C₁ * (l * k) ^ 2 := by ring
    have hR : l * ((θ₀ + C₁ * (2 + 2 * cb + ck) * g) * k +
        (θ₀ * cb + C₁ * (8 + 2 * cb + cb ^ 2)) * g ^ 2 * m) =
        l * (θ₀ * cb * g ^ 2 * m) + l * (θ₀ * k) + l * (C₁ * 8 * g ^ 2 * m) +
          l * (C₁ * 2 * cb * g ^ 2 * m) + l * (C₁ * 2 * g * k) + l * (C₁ * cb ^ 2 * g ^ 2 * m) +
          l * (C₁ * 2 * cb * g * k) + l * (C₁ * ck * g * k) := by ring
    rw [hexp, hR]
    linarith [e1, e2, e3, e4, e5, e6]
  exact le_of_mul_le_mul_left key hl0

set_option maxHeartbeats 1000000 in
/-- **The `ab` `K^{obs}` step in the linear regime**: as `kobsK_stepWAB`, with `k ≤ c_k m` in place
of `k ≤ c_k ḡ² m`. -/
theorem kobsK_stepWABL (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
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
      0 ≤ k → k ≤ ck * m → 0 ≤ ck → b + g / m * k ≤ ε₀ →
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
    (lam_trickL hm hg hg1 hk0 hθ0 hC₁ hb0 hb hcb hkk hck h2)

end

end Obs2
