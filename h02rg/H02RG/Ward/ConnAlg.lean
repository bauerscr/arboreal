import Mathlib

/-!
# The algebra of `cor:conn4pt`

`conn_alg`: from the scale-`N` identity
`1 - P = c² (-λ_aλ_b w² + γ_aγ_b + (-2λ_aλ_b w + λ_aγ_b + λ_bγ_a)/M + ẽ)`
and `cor:anm0` in the form `1 = c (Γ + Λ/M (1 + E))`, with `λ_{a,b} ≈ Λ`, `γ_{a,b} ≈ Γ`, `w ≈ G`,
`P = θ² + 2cΛθG + O(b²|G|² + bδ + bε + bη + be + b²ρ₁ + bρ₂)`, `θ = 1 - cΓ`
(the cancellations of the proof of `cor:conn4pt` in `h02rg.tex`).
-/

namespace Ward

theorem norm_mul_sub_mul_le (a b A B : ℂ) : ‖a * b - A * B‖ ≤ ‖a - A‖ * ‖b‖ + ‖A‖ * ‖b - B‖ := by
  have : a * b - A * B = (a - A) * b + A * (b - B) := by ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]

set_option maxHeartbeats 4000000 in
theorem conn_alg {c b M KΓ g δ ε η e ρ₁ ρ₂ : ℝ} {Λ Γ E G P la lb ga gb w et : ℂ}
    (hc : 0 < c) (hcb : c ≤ 2 * b) (hb1 : b ≤ 1) (hΛ : ‖Λ - 1‖ ≤ 1 / 2) (hΓ : ‖Γ‖ ≤ KΓ)
    (hE : ‖E‖ ≤ e) (he : e ≤ 1 / 2) (hG : ‖G‖ ≤ g) (hM : 0 < M)
    (hid : (1 : ℂ) = c * (Γ + Λ / M * (1 + E)))
    (hla : ‖la - Λ‖ ≤ δ) (hlb : ‖lb - Λ‖ ≤ δ) (hδ1 : δ ≤ 1)
    (hga : ‖ga - Γ‖ ≤ ε) (hgb : ‖gb - Γ‖ ≤ ε)
    (hw : ‖w - G‖ ≤ η) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (het : ‖et‖ ≤ ρ₁ + ρ₂ / M)
    (heq : 1 - P = (c : ℂ) ^ 2 * (-la * lb * w ^ 2 + ga * gb +
      (-2 * la * lb * w + la * gb + lb * ga) / M + et)) :
    ‖P - ((1 - c * Γ) ^ 2 + 2 * c * Λ * (1 - c * Γ) * G)‖ ≤
      200 * (1 + KΓ + g + ε + η) ^ 2 * (b ^ 2 * g ^ 2 + b * δ + b * ε + b * η + b * e + b ^ 2 * ρ₁ +
        b * ρ₂) := by
  set S := 1 + KΓ + g + ε + η with hS
  have hb : 0 < b := by linarith
  have hKΓ : 0 ≤ KΓ := (norm_nonneg _).trans hΓ
  have hg0 : 0 ≤ g := (norm_nonneg _).trans hG
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hla
  have hε : 0 ≤ ε := (norm_nonneg _).trans hga
  have hη : 0 ≤ η := (norm_nonneg _).trans hw
  have he0 : 0 ≤ e := (norm_nonneg _).trans hE
  have hS1 : 1 ≤ S := by rw [hS]; linarith
  have hρ : 0 ≤ ρ₁ + ρ₂ / M := (norm_nonneg _).trans het
  -- elementary bounds
  have nΛ : ‖Λ‖ ≤ 3 / 2 := by
    have := norm_sub_norm_le Λ 1; rw [norm_one] at this; linarith
  have nΛ' : 1 / 2 ≤ ‖Λ‖ := by
    have := norm_sub_norm_le (1 : ℂ) Λ; rw [norm_one, norm_sub_rev] at this; linarith
  have hΛ0 : Λ ≠ 0 := fun h => by rw [h, norm_zero] at nΛ'; linarith
  have n1E : 1 / 2 ≤ ‖1 + E‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-E)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this; linarith
  have h1E : (1 + E) ≠ 0 := fun h => by rw [h, norm_zero] at n1E; linarith
  have nlb : ‖lb‖ ≤ 5 / 2 := by
    have := norm_sub_norm_le lb Λ; linarith
  have nla : ‖la‖ ≤ 5 / 2 := by
    have := norm_sub_norm_le la Λ; linarith
  have ngb : ‖gb‖ ≤ S := by
    have := norm_sub_norm_le gb Γ; rw [hS]; linarith
  have nga : ‖ga‖ ≤ S := by
    have := norm_sub_norm_le ga Γ; rw [hS]; linarith
  have nw : ‖w‖ ≤ S := by
    have := norm_sub_norm_le w G; rw [hS]; linarith
  have nG : ‖G‖ ≤ S := by rw [hS]; linarith
  have nΓ : ‖Γ‖ ≤ S := by rw [hS]; linarith
  have hc2 : c ≤ 2 := by linarith
  have nθ : ‖(1 : ℂ) - c * Γ‖ ≤ 2 * S := by
    calc ‖(1 : ℂ) - c * Γ‖ ≤ 1 + c * ‖Γ‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
      _ ≤ 2 * S := by nlinarith
  -- `u = 1/M = θ/(cΛ(1+E))`
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hu : (1 / M : ℂ) = (1 - c * Γ) / (c * Λ * (1 + E)) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero hc0 hΛ0) h1E)]
    have h := hid
    field_simp at h ⊢
    linear_combination -h
  -- the main identity
  obtain ⟨θ, hθ⟩ : ∃ t : ℂ, t = 1 - c * Γ := ⟨_, rfl⟩
  rw [← hθ] at hu nθ ⊢
  obtain ⟨X, hX⟩ : ∃ t : ℂ, t = -2 * la * lb * w + la * gb + lb * ga := ⟨_, rfl⟩
  obtain ⟨X₀, hX₀⟩ : ∃ t : ℂ, t = -2 * Λ ^ 2 * G + 2 * Λ * Γ := ⟨_, rfl⟩
  obtain ⟨u₀, hu₀⟩ : ∃ t : ℂ, t = θ / (c * Λ) := ⟨_, rfl⟩
  have hk : (c : ℂ) * Λ * u₀ = θ := by
    rw [hu₀]; exact mul_div_cancel₀ θ (mul_ne_zero hc0 hΛ0)
  have hmain : (c : ℂ) ^ 2 * (-Λ ^ 2 * G ^ 2 + Γ ^ 2 + X₀ * u₀) =
      1 - (θ ^ 2 + 2 * c * Λ * θ * G) - (c : ℂ) ^ 2 * Λ ^ 2 * G ^ 2 := by
    have k1 : (c : ℂ) ^ 2 * (X₀ * u₀) = c * (-2 * Λ * G + 2 * Γ) * ((c : ℂ) * Λ * u₀) := by
      rw [hX₀]; ring
    rw [hk] at k1
    have k2 : (c : ℂ) ^ 2 * (-Λ ^ 2 * G ^ 2 + Γ ^ 2 + X₀ * u₀) =
        (c : ℂ) ^ 2 * (-Λ ^ 2 * G ^ 2 + Γ ^ 2) + (c : ℂ) ^ 2 * (X₀ * u₀) := by ring
    rw [k2, k1, hθ]
    ring
  have hdiff : P - (θ ^ 2 + 2 * c * Λ * θ * G) = (c : ℂ) ^ 2 * Λ ^ 2 * G ^ 2 -
      (c : ℂ) ^ 2 * ((-la * lb * w ^ 2 + Λ ^ 2 * G ^ 2) + (ga * gb - Γ * Γ) +
        (X - X₀) * (1 / M) + X₀ * ((1 / M) - u₀) + et) := by
    have h2 : P = 1 - (c : ℂ) ^ 2 * (-la * lb * w ^ 2 + ga * gb + X / M + et) := by
      rw [hX]; linear_combination -heq
    rw [h2]
    linear_combination -hmain
  -- pieces
  have T1 : ‖-la * lb * w ^ 2 + Λ ^ 2 * G ^ 2‖ ≤ 5 * S ^ 2 * (δ + η) := by
    have e1 : -la * lb * w ^ 2 + Λ ^ 2 * G ^ 2 = -((la * lb) * (w * w) - (Λ * Λ) * (G * G)) := by
      ring
    rw [e1, norm_neg]
    have a1 := norm_mul_sub_mul_le la lb Λ Λ
    have a2 := norm_mul_sub_mul_le w w G G
    have a3 := norm_mul_sub_mul_le (la * lb) (w * w) (Λ * Λ) (G * G)
    rw [norm_mul, norm_mul] at a3
    have b1 : ‖la * lb - Λ * Λ‖ ≤ 4 * δ := by
      refine a1.trans ?_
      have := mul_le_mul hla nlb (norm_nonneg _) hδ
      have := mul_le_mul nΛ hlb (norm_nonneg _) (by norm_num)
      linarith
    have b2 : ‖w * w - G * G‖ ≤ 2 * S * η := by
      refine a2.trans ?_
      have := mul_le_mul hw nw (norm_nonneg _) hη
      have := mul_le_mul nG hw (norm_nonneg _) (by linarith)
      linarith
    have hww : ‖w * w‖ ≤ S ^ 2 := by
      rw [norm_mul, sq]; exact mul_le_mul nw nw (norm_nonneg _) (by linarith)
    refine a3.trans ?_
    rw [← norm_mul] at a3 ⊢
    have hΛΛ : ‖Λ‖ * ‖Λ‖ ≤ 9 / 4 := by nlinarith [norm_nonneg Λ]
    calc ‖la * lb - Λ * Λ‖ * ‖w * w‖ + ‖Λ‖ * ‖Λ‖ * ‖w * w - G * G‖
        ≤ 4 * δ * S ^ 2 + 9 / 4 * (2 * S * η) := by
          gcongr
      _ ≤ 5 * S ^ 2 * (δ + η) := by
          have : S ≤ S ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right this hη, sq_nonneg S]
  have T2 : ‖ga * gb - Γ * Γ‖ ≤ 2 * S * ε := by
    refine (norm_mul_sub_mul_le ga gb Γ Γ).trans ?_
    have := mul_le_mul hga ngb (norm_nonneg _) hε
    have := mul_le_mul nΓ hgb (norm_nonneg _) (by linarith)
    linarith
  have T3 : ‖X - X₀‖ ≤ 10 * S * (δ + η + ε) := by
    have e1 : X - X₀ = -2 * ((la * lb) * w - (Λ * Λ) * G) + (la * gb - Λ * Γ) + (lb * ga - Λ * Γ) := by
      rw [hX, hX₀]; ring
    rw [e1]
    have a1 := norm_mul_sub_mul_le la lb Λ Λ
    have b1 : ‖la * lb - Λ * Λ‖ ≤ 4 * δ := by
      refine a1.trans ?_
      have := mul_le_mul hla nlb (norm_nonneg _) hδ
      have := mul_le_mul nΛ hlb (norm_nonneg _) (by norm_num)
      linarith
    have a2 := norm_mul_sub_mul_le (la * lb) w (Λ * Λ) G
    rw [norm_mul Λ Λ] at a2
    have hΛΛ : ‖Λ‖ * ‖Λ‖ ≤ 9 / 4 := by nlinarith [norm_nonneg Λ]
    have b2 : ‖la * lb * w - Λ * Λ * G‖ ≤ 4 * δ * S + 9 / 4 * η := by
      refine a2.trans ?_; gcongr
    have b3 : ‖la * gb - Λ * Γ‖ ≤ δ * S + 3 / 2 * ε := by
      refine (norm_mul_sub_mul_le la gb Λ Γ).trans ?_; gcongr
    have b4 : ‖lb * ga - Λ * Γ‖ ≤ δ * S + 3 / 2 * ε := by
      refine (norm_mul_sub_mul_le lb ga Λ Γ).trans ?_; gcongr
    calc ‖-2 * (la * lb * w - Λ * Λ * G) + (la * gb - Λ * Γ) + (lb * ga - Λ * Γ)‖
        ≤ ‖-2 * (la * lb * w - Λ * Λ * G)‖ + ‖la * gb - Λ * Γ‖ + ‖lb * ga - Λ * Γ‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = 2 * ‖la * lb * w - Λ * Λ * G‖ + ‖la * gb - Λ * Γ‖ + ‖lb * ga - Λ * Γ‖ := by
          rw [norm_mul]; norm_num
      _ ≤ 10 * S * (δ + η + ε) := by
          nlinarith [mul_le_mul_of_nonneg_right hS1 hη, mul_le_mul_of_nonneg_right hS1 hε,
            mul_le_mul_of_nonneg_right hS1 hδ]
  have T4 : ‖X₀‖ ≤ 8 * S := by
    calc ‖X₀‖ ≤ 2 * ‖Λ‖ ^ 2 * ‖G‖ + 2 * ‖Λ‖ * ‖Γ‖ := by
          rw [hX₀]
          refine (norm_add_le _ _).trans ?_
          simp only [norm_mul, norm_neg, norm_pow]; norm_num
      _ ≤ 8 * S := by
          have h1 : ‖Λ‖ ^ 2 ≤ 9 / 4 := by nlinarith [norm_nonneg Λ]
          have h2 := mul_le_mul h1 nG (norm_nonneg _) (by norm_num)
          have h3 := mul_le_mul nΛ nΓ (norm_nonneg _) (by norm_num)
          linarith
  have hcsq : (c : ℝ) ^ 2 ≤ 4 * b ^ 2 := by
    have := mul_le_mul hcb hcb hc.le (by linarith); nlinarith
  have hcsq' : (c : ℝ) ^ 2 ≤ 4 * b := by nlinarith
  have T5 : ‖(c : ℂ) ^ 2 * (1 / M)‖ ≤ 16 * b * S := by
    rw [hu, norm_mul, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hc.le]
    have hden : 1 / 4 * c ≤ c * ‖Λ‖ * ‖1 + E‖ := by
      have := mul_le_mul nΛ' n1E (by norm_num) (norm_nonneg _)
      nlinarith
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    calc c ^ 2 * ‖θ‖ ≤ c ^ 2 * (2 * S) := by gcongr
      _ ≤ 16 * b * S * (1 / 4 * c) := by
          have := mul_le_mul_of_nonneg_left hcb hc.le
          nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ S)]
      _ ≤ 16 * b * S * (c * ‖Λ‖ * ‖1 + E‖) := by gcongr
  have T6 : ‖(c : ℂ) ^ 2 * ((1 / M) - u₀)‖ ≤ 16 * b * S * e := by
    have e1 : (1 / M : ℂ) - u₀ = -(θ / (c * Λ)) * (E / (1 + E)) := by
      rw [hu, hu₀]; field_simp; ring
    rw [e1, norm_mul, norm_mul, norm_neg, norm_div, norm_mul, norm_div, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg hc.le]
    have h1 : ‖θ‖ / (c * ‖Λ‖) ≤ 4 * S / c := by
      rw [div_le_div_iff₀ (by positivity) hc]
      have h4 := mul_le_mul_of_nonneg_left nΛ' (by linarith : (0 : ℝ) ≤ 4 * S)
      have h5 : ‖θ‖ ≤ 4 * S * ‖Λ‖ := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h5 hc.le]
    have h2 : ‖E‖ / ‖1 + E‖ ≤ 2 * e := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc c ^ 2 * (‖θ‖ / (c * ‖Λ‖) * (‖E‖ / ‖1 + E‖)) ≤ c ^ 2 * (4 * S / c * (2 * e)) := by
          gcongr
      _ = 8 * c * S * e := by field_simp; ring
      _ ≤ 16 * b * S * e := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ S) he0]
  have T7 : ‖(c : ℂ) ^ 2 * et‖ ≤ 4 * b ^ 2 * ρ₁ + 16 * b * S * ρ₂ := by
    have e1 : ‖(c : ℂ) ^ 2 * et‖ ≤ c ^ 2 * ρ₁ + ‖(c : ℂ) ^ 2 * (1 / M)‖ * ρ₂ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc.le]
      have : ‖(c : ℂ) ^ 2 * (1 / M)‖ = c ^ 2 / M := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc.le, norm_div, norm_one,
          Complex.norm_real, Real.norm_of_nonneg hM.le]; ring
      rw [this]
      calc c ^ 2 * ‖et‖ ≤ c ^ 2 * (ρ₁ + ρ₂ / M) := by gcongr
        _ = c ^ 2 * ρ₁ + c ^ 2 / M * ρ₂ := by ring
    refine e1.trans ?_
    nlinarith [mul_le_mul_of_nonneg_right T5 hρ₂, mul_le_mul_of_nonneg_right hcsq hρ₁]
  -- assembly
  rw [hdiff]
  have hGG : ‖(c : ℂ) ^ 2 * Λ ^ 2 * G ^ 2‖ ≤ 9 * b ^ 2 * g ^ 2 := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hc.le]
    have h1 : ‖Λ‖ ^ 2 ≤ 9 / 4 := by nlinarith [norm_nonneg Λ]
    have h2 : ‖G‖ ^ 2 ≤ g ^ 2 := by nlinarith [norm_nonneg G]
    calc c ^ 2 * ‖Λ‖ ^ 2 * ‖G‖ ^ 2 ≤ (4 * b ^ 2) * (9 / 4) * g ^ 2 := by gcongr
      _ = 9 * b ^ 2 * g ^ 2 := by ring
  have hsum : ‖(c : ℂ) ^ 2 * ((-la * lb * w ^ 2 + Λ ^ 2 * G ^ 2) + (ga * gb - Γ * Γ) +
        (X - X₀) * (1 / M) + X₀ * ((1 / M) - u₀) + et)‖ ≤
      4 * b * (5 * S ^ 2 * (δ + η)) + 4 * b * (2 * S * ε) + 10 * S * (δ + η + ε) * (16 * b * S) +
        8 * S * (16 * b * S * e) + (4 * b ^ 2 * ρ₁ + 16 * b * S * ρ₂) := by
    have e1 : (c : ℂ) ^ 2 * ((-la * lb * w ^ 2 + Λ ^ 2 * G ^ 2) + (ga * gb - Γ * Γ) +
        (X - X₀) * (1 / M) + X₀ * ((1 / M) - u₀) + et) =
        (c : ℂ) ^ 2 * (-la * lb * w ^ 2 + Λ ^ 2 * G ^ 2) + (c : ℂ) ^ 2 * (ga * gb - Γ * Γ) +
        (X - X₀) * ((c : ℂ) ^ 2 * (1 / M)) + X₀ * ((c : ℂ) ^ 2 * ((1 / M) - u₀)) +
        (c : ℂ) ^ 2 * et := by ring
    rw [e1]
    have n1 : ‖(c : ℂ) ^ 2 * (-la * lb * w ^ 2 + Λ ^ 2 * G ^ 2)‖ ≤ 4 * b * (5 * S ^ 2 * (δ + η)) := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc.le]
      exact mul_le_mul hcsq' T1 (norm_nonneg _) (by positivity)
    have n2 : ‖(c : ℂ) ^ 2 * (ga * gb - Γ * Γ)‖ ≤ 4 * b * (2 * S * ε) := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc.le]
      exact mul_le_mul hcsq' T2 (norm_nonneg _) (by positivity)
    have n3 : ‖(X - X₀) * ((c : ℂ) ^ 2 * (1 / M))‖ ≤ 10 * S * (δ + η + ε) * (16 * b * S) := by
      rw [norm_mul]; exact mul_le_mul T3 T5 (norm_nonneg _) (by positivity)
    have n4 : ‖X₀ * ((c : ℂ) ^ 2 * ((1 / M) - u₀))‖ ≤ 8 * S * (16 * b * S * e) := by
      rw [norm_mul]; exact mul_le_mul T4 T6 (norm_nonneg _) (by positivity)
    calc _ ≤ ‖(c : ℂ) ^ 2 * (-la * lb * w ^ 2 + Λ ^ 2 * G ^ 2)‖ + ‖(c : ℂ) ^ 2 * (ga * gb - Γ * Γ)‖ +
          ‖(X - X₀) * ((c : ℂ) ^ 2 * (1 / M))‖ + ‖X₀ * ((c : ℂ) ^ 2 * ((1 / M) - u₀))‖ +
          ‖(c : ℂ) ^ 2 * et‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact norm_add_le _ _
      _ ≤ _ := by gcongr
  refine (norm_sub_le _ _).trans ((add_le_add hGG hsum).trans ?_)
  have hS0 : 0 ≤ S := by linarith
  have hSS : S ≤ S ^ 2 := by rw [sq]; exact le_mul_of_one_le_right hS0 hS1
  have h1S : 1 ≤ S ^ 2 := one_le_pow₀ hS1
  have q1 : 0 ≤ b ^ 2 * g ^ 2 := by positivity
  have q2 : 0 ≤ b * δ := mul_nonneg hb.le hδ
  have q3 : 0 ≤ b * η := mul_nonneg hb.le hη
  have q4 : 0 ≤ b * ε := mul_nonneg hb.le hε
  have q5 : 0 ≤ b * e := mul_nonneg hb.le he0
  have q6 : 0 ≤ b ^ 2 * ρ₁ := by positivity
  have q7 : 0 ≤ b * ρ₂ := mul_nonneg hb.le hρ₂
  have r1 := mul_le_mul_of_nonneg_right h1S q1
  have r2 := mul_le_mul_of_nonneg_right h1S q2
  have r3 := mul_le_mul_of_nonneg_right h1S q3
  have r4 := mul_le_mul_of_nonneg_right h1S q4
  have r5 := mul_le_mul_of_nonneg_right h1S q5
  have r6 := mul_le_mul_of_nonneg_right h1S q6
  have r7 := mul_le_mul_of_nonneg_right hSS q4
  have r8 := mul_le_mul_of_nonneg_right hSS q7
  have r9 := mul_le_mul_of_nonneg_right hSS q7
  have e1 : 9 * b ^ 2 * g ^ 2 + (4 * b * (5 * S ^ 2 * (δ + η)) + 4 * b * (2 * S * ε) +
      10 * S * (δ + η + ε) * (16 * b * S) + 8 * S * (16 * b * S * e) +
      (4 * b ^ 2 * ρ₁ + 16 * b * S * ρ₂)) =
      9 * (b ^ 2 * g ^ 2) + 180 * (S ^ 2 * (b * δ)) + 180 * (S ^ 2 * (b * η)) +
      8 * (S * (b * ε)) + 160 * (S ^ 2 * (b * ε)) + 128 * (S ^ 2 * (b * e)) +
      4 * (b ^ 2 * ρ₁) + 16 * (S * (b * ρ₂)) := by ring
  have e2 : 200 * S ^ 2 * (b ^ 2 * g ^ 2 + b * δ + b * ε + b * η + b * e + b ^ 2 * ρ₁ +
      b * ρ₂) = 200 * (S ^ 2 * (b ^ 2 * g ^ 2)) + 200 * (S ^ 2 * (b * δ)) +
      200 * (S ^ 2 * (b * ε)) + 200 * (S ^ 2 * (b * η)) + 200 * (S ^ 2 * (b * e)) +
      200 * (S ^ 2 * (b ^ 2 * ρ₁)) + 200 * (S ^ 2 * (b * ρ₂)) := by ring
  rw [e1, e2]
  have z1 := mul_nonneg (sq_nonneg S) q1
  have z2 := mul_nonneg (sq_nonneg S) q2
  have z3 := mul_nonneg (sq_nonneg S) q3
  have z4 := mul_nonneg (sq_nonneg S) q4
  have z5 := mul_nonneg (sq_nonneg S) q5
  have z6 := mul_nonneg (sq_nonneg S) q6
  have z7 := mul_nonneg (sq_nonneg S) q7
  rw [one_mul] at r1 r6
  linarith

end Ward
