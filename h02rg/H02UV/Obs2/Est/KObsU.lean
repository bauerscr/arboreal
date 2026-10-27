import Obs2.Est.StepKOWU
import Obs2.Est.EstLocU

/-!
# The `σ_aσ_b` part of the activity step for unreduced inputs (copy of `Obs2.Est.KObsAB`)

**`kobsK_stepWU`**: for unreduced inputs (one-point parts present, all four components local,
`OLocS`, `U(1)` invariance, `K(X)_{ab} = 0` on small sets as below coalescence) and finite
weights with `w.Sub`: with `‖V^∅‖ ≤ ḡ/2`, `‖V^{obs}‖_w ≤ m`, `‖𝒲^{obs}‖_w ≤ ḡm` (`ḡ ≤ 2m`), the
one-point part `A^{(…)}‖K^{obs}(X)‖_{(w_a,w_b,0)} ≤ k₁` and the `ab` part
`A^{(…)}w_{ab}‖K(X)_{ab}‖ ≤ k₂`, the `ab` part of `K_{j+1} = KplusO` obeys, with `λ = ḡ/(2m)`,

  `λ²(μA)^{(|𝓑_{j+1}(U)|-2^d)_+} w_{ab}‖K_{j+1}(U)_{ab}‖ ≤ θ₀k_t + C₁(ḡ³ + ḡk_t + k_t²)`,
  `k_t = b + λk₁ + λ²k₂`, `θ₀ = C₀(L^{d-3} + A^{-η})`.

Proof: `stepKO_tsWU` in the rescaled weights `w_λ = (λw_a, λw_b, λ²w_{ab})` (`oTo_scale_eq`):
`‖V‖_{w_λ} ≤ λm = ḡ/2`, `‖𝒲‖_{w_λ} ≤ ḡ²/2` (`λ ≤ 1`), `‖K‖_{w_λ} = λ‖K‖_{(w_a,w_b,0)} + λ²w_{ab}‖K_{ab}‖`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

theorem oTo_scale_eq (w : Wt) (lam : ℝ≥0∞) (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) :
    oTo (Wt.scale lam w) j ℓ F =
      lam * oTo (wOne w) j ℓ F + lam ^ 2 * (w.ab * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab) := by
  have hz : Tj d (L : ℝ) j ℓ (0 : Alg d L N) = 0 := tNorm_zero'
  simp only [oTo, oTj, oNorm, Wt.scale, wOne, coe_πobs, piobs_apply, hz]
  ring

theorem oTo_scale_le (w : Wt) {lam : ℝ≥0∞} (hl : lam ≤ 1) (j : ℕ) (ℓ : ℝ)
    (F : OE c (Lam d L N)) : oTo (Wt.scale lam w) j ℓ F ≤ lam * oTo w j ℓ F := by
  rw [oTo_scale_eq, oTo_split_ab w j ℓ F, mul_add]
  refine add_le_add le_rfl (mul_le_mul_right' ?_ _)
  calc lam ^ 2 = lam * lam := pow_two lam
    _ ≤ lam * 1 := mul_le_mul_left' hl _
    _ = lam := mul_one lam

set_option maxHeartbeats 1000000 in
/-- **The `ab` part of the activity step, unreduced inputs.** -/
theorem kobsK_stepWU (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ μ : ℝ, 1 ≤ μ → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.Sub → w.a ≠ ⊤ → w.b ≠ ⊤ → w.ab ≠ ⊤ →
    ∀ (V W : OFam c d L N) (K : OAct c d L N),
      InF j (bulkF V) → InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam d L N)) : Alg d L N) = 0) → InK2 j (bulkF K) →
      OLocS P j V W K →
      (∀ X, IsConn j X → IsSymS (K X : SA c (Lam d L N))) →
      (∀ X, IsSmall j X → (K X : SA c (Lam d L N)).ab = 0) →
      ∀ g m b k₁ k₂ : ℝ, 0 < g → 0 < m → g ≤ 2 * m → 0 ≤ b → 0 ≤ k₁ → 0 ≤ k₂ → g ≤ ε₀ →
      b + g / (2 * m) * k₁ + (g / (2 * m)) ^ 2 * k₂ ≤ ε₀ →
      Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal (g / 2) → Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal (g ^ 2) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal m) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal (g * m)) →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal b →
      (∀ X, IsConn j X →
        ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo (wOne w) j ℓ (K X) ≤ ENNReal.ofReal k₁) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) *
        (w.ab * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).ab) ≤ ENNReal.ofReal k₂) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal ((g / (2 * m)) ^ 2) * (ENNReal.ofReal ((μ * A) ^ (nb (j + 1) U - 2 ^ d)) *
          (w.ab * Tj d (L : ℝ) (j + 1) ℓ' (KplusO P j C V W K U : SA c (Lam d L N)).ab)) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) *
              (b + g / (2 * m) * k₁ + (g / (2 * m)) ^ 2 * k₂) +
            C₁ * (g ^ 3 + g * (b + g / (2 * m) * k₁ + (g / (2 * m)) ^ 2 * k₂) +
              (b + g / (2 * m) * k₁ + (g / (2 * m)) ^ 2 * k₂) ^ 2)) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := stepKO_tsWU d hd
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL μ hμ => ?_⟩
  obtain ⟨A₀, hA₀, h⟩ := h L hL μ hμ
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε₀, C₁, hε₀, hC₁, h⟩ := h A hA
  refine ⟨ε₀, C₁, hε₀, hC₁, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw hwa hwb hwab V W K hV hW hV0 hK HL
    hsym hKs g m b k₁ k₂ hg hm hgm hb0 hk₁ hk₂ hgε hkε hVg hWg hVo hWo hKb hK1 hK2 U hU
  set l := g / (2 * m) with hl
  have hl0 : 0 < l := div_pos hg (by linarith)
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by linarith)]; exact hgm
  have hlm : l * m = g / 2 := by rw [hl]; field_simp
  have hl1' : ENNReal.ofReal l ≤ 1 := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hl1
  set wl := Wt.scale (ENNReal.ofReal l) w with hwl
  have hwl0 : wl.Sub := Wt.scale_sub hw _
  have hwlab : wl.ab ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hwab
  have hwla : wl.a ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwa
  have hwlb : wl.b ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwb
  set kt := b + l * k₁ + l ^ 2 * k₂ with hkt
  have hkt0 : 0 ≤ kt := by positivity
  have hza : ∀ X, IsConn j X → P.a ∉ nbhd j X → (K X : SA c (Lam d L N)).a = 0 :=
    fun X hX ha => osub_a_zero (HL.hK X hX) ha
  have hzb : ∀ X, IsConn j X → P.b ∉ nbhd j X → (K X : SA c (Lam d L N)).b = 0 :=
    fun X hX hb => osub_b_zero (HL.hK X hX) hb
  have H := h N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P wl hwl0 hwla hwlb hwlab V W K hza hzb hKs
    hV hW hV0 hK HL hsym g hg.le hgε hVg hWg
    (fun b' hb' => by
      refine (oTo_scale_le w hl1' j ℓ _).trans ?_
      rw [← hlm, ENNReal.ofReal_mul hl0.le]
      exact mul_le_mul_left' (hVo b' hb') _)
    (fun b' hb' => by
      refine (oTo_scale_le w hl1' j ℓ _).trans ?_
      have e : g ^ 2 = l * (g * m) * 2 := by rw [hl]; field_simp
      calc ENNReal.ofReal l * oTo w j ℓ (W b') ≤ ENNReal.ofReal l * ENNReal.ofReal (g * m) :=
            mul_le_mul_left' (hWo b' hb') _
        _ = ENNReal.ofReal (l * (g * m)) := (ENNReal.ofReal_mul hl0.le).symm
        _ ≤ ENNReal.ofReal (g ^ 2) := ENNReal.ofReal_le_ofReal (by
            rw [e]; have : 0 ≤ l * (g * m) := by positivity
            linarith))
    kt hkt0 hkε (hKb.trans (ENNReal.ofReal_le_ofReal (by
      have : 0 ≤ l * k₁ + l ^ 2 * k₂ := by positivity
      rw [hkt]; linarith)))
    (fun X hX => by
      rw [oTo_scale_eq, mul_add, mul_left_comm, mul_left_comm (ENNReal.ofReal (A ^ _))]
      calc ENNReal.ofReal l * (ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo (wOne w) j ℓ (K X)) +
            ENNReal.ofReal l ^ 2 * (ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) *
              (w.ab * Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).ab))
          ≤ ENNReal.ofReal l * ENNReal.ofReal k₁ + ENNReal.ofReal l ^ 2 * ENNReal.ofReal k₂ :=
            add_le_add (mul_le_mul_left' (hK1 X hX) _) (mul_le_mul_left' (hK2 X hX) _)
        _ = ENNReal.ofReal (l * k₁ + l ^ 2 * k₂) := by
            rw [← ENNReal.ofReal_pow hl0.le, ← ENNReal.ofReal_mul hl0.le,
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal kt := ENNReal.ofReal_le_ofReal (by rw [hkt]; linarith))
    U hU
  set wt : ℝ := (μ * A) ^ (nb (j + 1) U - 2 ^ d)
  set F := KplusO P j C V W K U
  have hlow : ENNReal.ofReal (l ^ 2) * (w.ab * Tj d (L : ℝ) (j + 1) ℓ' (F : SA c (Lam d L N)).ab) ≤
      oTj d L wl (j + 1) ℓ' (F : SA c (Lam d L N)) := by
    rw [oTj_eq_bulk_add, oTo_scale_eq, ENNReal.ofReal_pow hl0.le]
    exact le_add_left le_add_self
  calc ENNReal.ofReal (l ^ 2) * (ENNReal.ofReal wt *
        (w.ab * Tj d (L : ℝ) (j + 1) ℓ' (F : SA c (Lam d L N)).ab))
      = ENNReal.ofReal wt * (ENNReal.ofReal (l ^ 2) *
          (w.ab * Tj d (L : ℝ) (j + 1) ℓ' (F : SA c (Lam d L N)).ab)) := by ring
    _ ≤ ENNReal.ofReal wt * oTj d L wl (j + 1) ℓ' (F : SA c (Lam d L N)) := mul_le_mul_left' hlow _
    _ ≤ _ := H
    _ = _ := by
        have hA0 : (0 : ℝ) ≤ A := by linarith
        have hθ : 0 ≤ C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) := by
          have := Real.rpow_nonneg hA0 (-η); positivity
        have h1 : 0 ≤ C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) * kt := mul_nonneg hθ hkt0
        have h2 : 0 ≤ C₁ * (g ^ 3 + g * kt + kt ^ 2) := by positivity
        exact (ENNReal.ofReal_add h1 h2).symm

end

end Obs2
