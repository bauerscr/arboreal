import Step2.Lip.FlowLipG

/-!
# Assembly of the bounds for `G` and `m` (Lipschitz bounds, part 26)

Pure real-number lemmas with a single constant `K ≥ 1` and the small parameter `σ = e + ε ≤ 2`:
the bounds of the individual pieces combine to (LG) (`G_assemble`) and (Lm) (`m_assemble`).
-/

namespace Step2

noncomputable section

/-- The common bounds of the pieces. -/
structure Pieces (K σ ε dx dg dμ M dĝ Θ : ℝ) : Prop where
  hK : 1 ≤ K
  hσ : 0 ≤ σ
  hσ2 : σ ≤ 2
  hεσ : ε ≤ σ
  hε : 0 ≤ ε
  hdx : 0 ≤ dx
  hdg : 0 ≤ dg
  hdμ : 0 ≤ dμ
  hM : 0 ≤ M
  hĝ : dĝ ≤ dg + σ * (4 * K) * (dx + dg + dμ + M)
  hΘ : Θ ≤ K * dx + σ * K * (dx + dg + dμ + M)
  hΘ0 : 0 ≤ Θ
  hĝ0 : 0 ≤ dĝ

namespace Pieces

variable {K σ ε dx dg dμ M dĝ Θ : ℝ} (H : Pieces K σ ε dx dg dμ M dĝ Θ)
include H

theorem Q0 : 0 ≤ dx + dg + dμ + M := by have := H.hdx; have := H.hdg; have := H.hdμ; have := H.hM; linarith

theorem ĝQ : dĝ ≤ (1 + 8 * K) * (dx + dg + dμ + M) := by
  have h1 := H.hĝ
  have hQ := H.Q0
  have h2 : σ * (4 * K) * (dx + dg + dμ + M) ≤ 2 * (4 * K) * (dx + dg + dμ + M) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right H.hσ2 (by linarith [H.hK])) hQ
  have h3 : dg ≤ dx + dg + dμ + M := by have := H.hdx; have := H.hdμ; have := H.hM; linarith
  nlinarith

theorem ΘQ : Θ ≤ 3 * K * (dx + dg + dμ + M) := by
  have hQ := H.Q0
  have h2 : σ * K * (dx + dg + dμ + M) ≤ 2 * K * (dx + dg + dμ + M) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right H.hσ2 (by linarith [H.hK])) hQ
  have h3 : K * dx ≤ K * (dx + dg + dμ + M) :=
    mul_le_mul_of_nonneg_left (by have := H.hdg; have := H.hdμ; have := H.hM; linarith)
      (by linarith [H.hK])
  linarith [H.hΘ]

end Pieces

/-- **Assembly for `G`.** -/
theorem G_assemble {K σ ε dx dg dμ M dĝ Θ d3 dζ dν dw dn1 dG s B3 : ℝ}
    (H : Pieces K σ ε dx dg dμ M dĝ Θ) (hs : s ≤ σ * K) (hs0 : 0 ≤ s) (hB3 : B3 ≤ σ * K)
    (hB30 : 0 ≤ B3)
    (h3 : d3 ≤ K * Θ + dĝ) (hζ : dζ ≤ K * Θ + K * dĝ + σ * K * M)
    (hν : dν ≤ K * (Θ + dμ + dĝ + M)) (hw : dw ≤ K * M) (hn : dn1 ≤ K * (dν + dw))
    (hζ0 : 0 ≤ dζ) (hn0 : 0 ≤ dn1) (h30 : 0 ≤ d3)
    (hG : dG ≤ (1 + 4 * s) * d3 + B3 * (2 * dn1 + 5 * dζ)) :
    dG ≤ (1 + σ * (200 * K ^ 4)) * dg + σ * (200 * K ^ 4) * dμ + 500 * K ^ 4 * dx +
      σ * (200 * K ^ 4) * M := by
  have hK := H.hK
  have hK0 : 0 ≤ K := by linarith
  have hσ := H.hσ
  have hQ := H.Q0
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = dx + dg + dμ + M := ⟨_, rfl⟩
  rw [← hQd] at hQ
  have hĝQ : dĝ ≤ (1 + 8 * K) * Q := hQd ▸ H.ĝQ
  have hΘQ : Θ ≤ 3 * K * Q := hQd ▸ H.ΘQ
  have hĝ : dĝ ≤ dg + σ * (4 * K) * Q := hQd ▸ H.hĝ
  have hΘ : Θ ≤ K * dx + σ * K * Q := hQd ▸ H.hΘ
  have hxQ : dx ≤ Q := by have := H.hdg; have := H.hdμ; have := H.hM; linarith
  have hgQ : dg ≤ Q := by have := H.hdx; have := H.hdμ; have := H.hM; linarith
  have hμQ : dμ ≤ Q := by have := H.hdx; have := H.hdg; have := H.hM; linarith
  have hMQ : M ≤ Q := by have := H.hdx; have := H.hdg; have := H.hdμ; linarith
  have hKK : K ≤ K ^ 2 := by nlinarith
  have hK2 : K ^ 2 ≤ K ^ 3 := by nlinarith
  have hK3 : K ^ 3 ≤ K ^ 4 := by nlinarith
  -- d3
  have h3' : d3 ≤ K ^ 2 * dx + dg + σ * (K ^ 2 + 4 * K) * Q := by
    have a1 := mul_le_mul_of_nonneg_left hΘ hK0
    have e1 : K * (K * dx + σ * K * Q) = K ^ 2 * dx + σ * K ^ 2 * Q := by ring
    have e2 : σ * (K ^ 2 + 4 * K) * Q = σ * K ^ 2 * Q + σ * (4 * K) * Q := by ring
    linarith only [h3, a1, e1, e2, hĝ]
  have h3Q : d3 ≤ (3 * K ^ 2 + 8 * K + 1) * Q := by
    have a1 : K ^ 2 * dx ≤ K ^ 2 * Q := mul_le_mul_of_nonneg_left hxQ (by positivity)
    have a3 : σ * (K ^ 2 + 4 * K) * Q ≤ 2 * (K ^ 2 + 4 * K) * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right H.hσ2 (by positivity)) hQ
    have e1 : (3 * K ^ 2 + 8 * K + 1) * Q = K ^ 2 * Q + Q + 2 * (K ^ 2 + 4 * K) * Q := by ring
    linarith only [h3', a1, hgQ, a3, e1]
  -- dζ, dν, dn1
  have hζQ : dζ ≤ 14 * K ^ 2 * Q := by
    have a1 := mul_le_mul_of_nonneg_left hΘQ hK0
    have a2 := mul_le_mul_of_nonneg_left hĝQ hK0
    have a3 : σ * K * M ≤ 2 * K * Q :=
      mul_le_mul (mul_le_mul_of_nonneg_right H.hσ2 hK0) hMQ H.hM (by positivity)
    have a4 : K * Q ≤ K ^ 2 * Q := mul_le_mul_of_nonneg_right hKK hQ
    have e1 : K * (3 * K * Q) = 3 * K ^ 2 * Q := by ring
    have e2 : K * ((1 + 8 * K) * Q) = K * Q + 8 * K ^ 2 * Q := by ring
    linarith only [hζ, a1, a2, a3, a4, e1, e2]
  have hνQ : dν ≤ 14 * K ^ 2 * Q := by
    have h1 : Θ + dμ + dĝ + M ≤ (11 * K + 3) * Q := by
      have e1 : (11 * K + 3) * Q = 3 * K * Q + Q + (1 + 8 * K) * Q + Q := by ring
      linarith only [hΘQ, hμQ, hĝQ, hMQ, e1]
    have a1 := mul_le_mul_of_nonneg_left h1 hK0
    have a4 : K * Q ≤ K ^ 2 * Q := mul_le_mul_of_nonneg_right hKK hQ
    have e1 : K * ((11 * K + 3) * Q) = 11 * K ^ 2 * Q + 3 * (K * Q) := by ring
    linarith only [hν, a1, a4, e1]
  have hwQ : dw ≤ K * Q := hw.trans (mul_le_mul_of_nonneg_left hMQ hK0)
  have hnQ : dn1 ≤ 15 * K ^ 3 * Q := by
    have a1 := mul_le_mul_of_nonneg_left (add_le_add hνQ hwQ) hK0
    have e1 : K * (14 * K ^ 2 * Q + K * Q) = 14 * K ^ 3 * Q + K ^ 2 * Q := by ring
    have a2 : K ^ 2 * Q ≤ K ^ 3 * Q := mul_le_mul_of_nonneg_right hK2 hQ
    linarith only [hn, a1, e1, a2]
  -- assemble
  have t1 : (1 + 4 * s) * d3 ≤ d3 + 4 * σ * K * ((3 * K ^ 2 + 8 * K + 1) * Q) := by
    have a1 := mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4)) h3Q h30
      (by positivity)
    have e1 : (1 + 4 * s) * d3 = d3 + 4 * s * d3 := by ring
    have e2 : 4 * (σ * K) * ((3 * K ^ 2 + 8 * K + 1) * Q) =
        4 * σ * K * ((3 * K ^ 2 + 8 * K + 1) * Q) := by ring
    linarith only [a1, e1, e2]
  have t2 : B3 * (2 * dn1 + 5 * dζ) ≤ σ * K * ((30 * K ^ 3 + 70 * K ^ 2) * Q) := by
    have a1 : 2 * dn1 + 5 * dζ ≤ (30 * K ^ 3 + 70 * K ^ 2) * Q := by
      have e1 : (30 * K ^ 3 + 70 * K ^ 2) * Q = 2 * (15 * K ^ 3 * Q) + 5 * (14 * K ^ 2 * Q) := by ring
      linarith only [hnQ, hζQ, e1]
    exact mul_le_mul hB3 a1 (by positivity) (by positivity)
  have hS : σ * (K ^ 2 + 4 * K) * Q + 4 * σ * K * ((3 * K ^ 2 + 8 * K + 1) * Q) +
      σ * K * ((30 * K ^ 3 + 70 * K ^ 2) * Q) ≤ σ * (200 * K ^ 4) * Q := by
    have h1 : (K ^ 2 + 4 * K) + 4 * K * (3 * K ^ 2 + 8 * K + 1) + K * (30 * K ^ 3 + 70 * K ^ 2) ≤
        200 * K ^ 4 := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hσ hQ)
    have e1 : σ * (K ^ 2 + 4 * K) * Q + 4 * σ * K * ((3 * K ^ 2 + 8 * K + 1) * Q) +
        σ * K * ((30 * K ^ 3 + 70 * K ^ 2) * Q) = σ * Q * ((K ^ 2 + 4 * K) +
          4 * K * (3 * K ^ 2 + 8 * K + 1) + K * (30 * K ^ 3 + 70 * K ^ 2)) := by ring
    have e2 : σ * (200 * K ^ 4) * Q = σ * Q * (200 * K ^ 4) := by ring
    linarith only [this, e1, e2]
  have hdx' : K ^ 2 * dx ≤ 100 * K ^ 4 * dx := by
    have : K ^ 2 ≤ 100 * K ^ 4 := by nlinarith
    exact mul_le_mul_of_nonneg_right this H.hdx
  have hσx : σ * (200 * K ^ 4) * dx ≤ 400 * K ^ 4 * dx := by
    have hx := H.hdx
    have := mul_le_mul_of_nonneg_right H.hσ2 (by positivity : (0 : ℝ) ≤ 200 * K ^ 4 * dx)
    linarith only [this, show σ * (200 * K ^ 4) * dx = σ * (200 * K ^ 4 * dx) by ring]
  have eQ : σ * (200 * K ^ 4) * Q = σ * (200 * K ^ 4) * dx + σ * (200 * K ^ 4) * dg +
      σ * (200 * K ^ 4) * dμ + σ * (200 * K ^ 4) * M := by rw [hQd]; ring
  have e3 : (1 + σ * (200 * K ^ 4)) * dg = dg + σ * (200 * K ^ 4) * dg := by ring
  linarith only [hG, t1, t2, h3', hS, hdx', hσx, eQ, e3]

/-- **Assembly for `m`.** -/
theorem m_assemble {K σ ε dx dg dμ M dĝ Θ dζ dY dP dm Pn ϑ : ℝ}
    (H : Pieces K σ ε dx dg dμ M dĝ Θ) (hϑ : 0 ≤ ϑ) (hPn : Pn ≤ σ * K) (hPn0 : 0 ≤ Pn)
    (hζ : dζ ≤ K * Θ + K * dĝ + σ * K * M) (hζ0 : 0 ≤ dζ)
    (hY : dY ≤ K * (Θ + dĝ) + ϑ * K * M + σ * K * M)
    (hP : dP ≤ dY + σ * K * dμ + σ * K * dζ)
    (hm : dm ≤ 2 * dP + 2 * Pn * dζ) :
    dm ≤ 300 * K ^ 4 * (dg + dx) + σ * (300 * K ^ 4) * dμ + (σ * (300 * K ^ 4) + 2 * K * ϑ) * M := by
  have hK := H.hK
  have hK0 : 0 ≤ K := by linarith
  have hσ := H.hσ
  have hQ := H.Q0
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = dx + dg + dμ + M := ⟨_, rfl⟩
  rw [← hQd] at hQ
  have hĝQ : dĝ ≤ (1 + 8 * K) * Q := hQd ▸ H.ĝQ
  have hΘQ : Θ ≤ 3 * K * Q := hQd ▸ H.ΘQ
  have hĝ : dĝ ≤ dg + σ * (4 * K) * Q := hQd ▸ H.hĝ
  have hΘ : Θ ≤ K * dx + σ * K * Q := hQd ▸ H.hΘ
  have hMQ : M ≤ Q := by have := H.hdx; have := H.hdg; have := H.hdμ; linarith
  have hμQ : dμ ≤ Q := by have := H.hdx; have := H.hdg; have := H.hM; linarith
  have hKK : K ≤ K ^ 2 := by nlinarith
  have hK2 : K ^ 2 ≤ K ^ 3 := by nlinarith
  have hK3 : K ^ 3 ≤ K ^ 4 := by nlinarith
  have hζQ : dζ ≤ 14 * K ^ 2 * Q := by
    have a1 := mul_le_mul_of_nonneg_left hΘQ hK0
    have a2 := mul_le_mul_of_nonneg_left hĝQ hK0
    have a3 : σ * K * M ≤ 2 * K * Q :=
      mul_le_mul (mul_le_mul_of_nonneg_right H.hσ2 hK0) hMQ H.hM (by positivity)
    have a4 : K * Q ≤ K ^ 2 * Q := mul_le_mul_of_nonneg_right hKK hQ
    have e1 : K * (3 * K * Q) = 3 * K ^ 2 * Q := by ring
    have e2 : K * ((1 + 8 * K) * Q) = K * Q + 8 * K ^ 2 * Q := by ring
    linarith only [hζ, a1, a2, a3, a4, e1, e2]
  have hY' : dY ≤ K ^ 2 * dx + K * dg + σ * (5 * K ^ 2) * Q + ϑ * K * M + σ * K * M := by
    have a1 := mul_le_mul_of_nonneg_left (add_le_add hΘ hĝ) hK0
    have e1 : K * (K * dx + σ * K * Q + (dg + σ * (4 * K) * Q)) =
        K ^ 2 * dx + K * dg + σ * (5 * K ^ 2) * Q := by ring
    linarith only [hY, a1, e1]
  have hσζ : σ * K * dζ ≤ σ * (14 * K ^ 3) * Q := by
    have := mul_le_mul_of_nonneg_left hζQ (mul_nonneg hσ hK0)
    linarith only [this, show σ * K * (14 * K ^ 2 * Q) = σ * (14 * K ^ 3) * Q by ring]
  have hPζ : Pn * dζ ≤ σ * (14 * K ^ 3) * Q := by
    have := mul_le_mul hPn hζQ hζ0 (by positivity)
    linarith only [this, show σ * K * (14 * K ^ 2 * Q) = σ * (14 * K ^ 3) * Q by ring]
  have hσμ : σ * K * dμ ≤ σ * K * Q := mul_le_mul_of_nonneg_left hμQ (by positivity)
  have hσM : σ * K * M ≤ σ * K * Q := mul_le_mul_of_nonneg_left hMQ (by positivity)
  -- dm ≤ 2K²dx + 2K dg + σ C Q + 2ϑ K M
  have h1 : dm ≤ 2 * K ^ 2 * dx + 2 * K * dg + σ * (10 * K ^ 2 + 4 * K + 56 * K ^ 3) * Q +
      2 * ϑ * K * M := by
    have e1 : σ * (10 * K ^ 2 + 4 * K + 56 * K ^ 3) * Q = 2 * (σ * (5 * K ^ 2) * Q) +
        2 * (σ * K * Q) + 2 * (σ * K * Q) + 2 * (σ * (14 * K ^ 3) * Q) +
          2 * (σ * (14 * K ^ 3) * Q) := by ring
    linarith only [hm, hP, hY', hσζ, hPζ, hσμ, hσM, e1]
  have hC : 10 * K ^ 2 + 4 * K + 56 * K ^ 3 ≤ 70 * K ^ 4 := by nlinarith
  have h2 : σ * (10 * K ^ 2 + 4 * K + 56 * K ^ 3) * Q ≤ σ * (70 * K ^ 4) * Q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hσ) hQ
  have eQ : σ * (70 * K ^ 4) * Q = σ * (70 * K ^ 4) * dx + σ * (70 * K ^ 4) * dg +
      σ * (70 * K ^ 4) * dμ + σ * (70 * K ^ 4) * M := by rw [hQd]; ring
  have hx := H.hdx
  have hg := H.hdg
  have hμ := H.hdμ
  have hM := H.hM
  have b1 : σ * (70 * K ^ 4) * dx ≤ 140 * K ^ 4 * dx := by
    have := mul_le_mul_of_nonneg_right H.hσ2 (by positivity : (0 : ℝ) ≤ 70 * K ^ 4 * dx)
    linarith only [this, show σ * (70 * K ^ 4) * dx = σ * (70 * K ^ 4 * dx) by ring]
  have b2 : σ * (70 * K ^ 4) * dg ≤ 140 * K ^ 4 * dg := by
    have := mul_le_mul_of_nonneg_right H.hσ2 (by positivity : (0 : ℝ) ≤ 70 * K ^ 4 * dg)
    linarith only [this, show σ * (70 * K ^ 4) * dg = σ * (70 * K ^ 4 * dg) by ring]
  have b3 : 2 * K ^ 2 * dx ≤ 2 * K ^ 4 * dx := by
    have : K ^ 2 ≤ K ^ 4 := le_trans hK2 hK3
    have := mul_le_mul_of_nonneg_right this hx
    linarith only [this]
  have b4 : 2 * K * dg ≤ 2 * K ^ 4 * dg := by
    have : K ≤ K ^ 4 := le_trans hKK (le_trans hK2 hK3)
    have := mul_le_mul_of_nonneg_right this hg
    linarith only [this]
  have hK4' : 0 ≤ K ^ 4 := by positivity
  have b5 : σ * (70 * K ^ 4) * dμ ≤ σ * (300 * K ^ 4) * dμ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [hK4']) hσ) hμ
  have b6 : σ * (70 * K ^ 4) * M ≤ σ * (300 * K ^ 4) * M :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [hK4']) hσ) hM
  have e2 : 300 * K ^ 4 * (dg + dx) = 300 * K ^ 4 * dg + 300 * K ^ 4 * dx := by ring
  have e3 : (σ * (300 * K ^ 4) + 2 * K * ϑ) * M = σ * (300 * K ^ 4) * M + 2 * ϑ * K * M := by ring
  have hK4 : 0 ≤ K ^ 4 := by positivity
  have b7 : 142 * K ^ 4 * dx ≤ 300 * K ^ 4 * dx := by
    have := mul_nonneg hK4 hx; linarith only [this]
  have b8 : 142 * K ^ 4 * dg ≤ 300 * K ^ 4 * dg := by
    have := mul_nonneg hK4 hg; linarith only [this]
  linarith only [h1, h2, eQ, b1, b2, b3, b4, b5, b6, e2, e3, b7, b8]

end

end Step2
