import PtCorr.LamOne

/-!
# Lemma `lem:2pt`, Case (1): the two-point function `⟨ψ̄_a ψ_b⟩` (`e:2pt-a`, Tier 1)

Finite `N`, `m² > 0`, couplings of scale `N`.  With `a = ctr`, `b = a + x`, `x ≠ 0`,
`r = |x|_∞`, `W = W_N(x)`, `τ = t_N/|Λ|`, `ũ = ũ_{N,N}` and `1 + ũ ≠ 0` (**`lem_2pt_one`**):

  `⟨ψ̄_a ψ_b⟩ = W + (τ + E₂)/(1 + ũ) + E₁`,
  `|E₁| ≤ C|b₀| r^{-(d-2+κ)}`,  `|E₂| ≤ C|b₀| (r^{-κ}/(m²|Λ|) + L^{-(d-2+κ)N})`,

and the same for `⟨ψ̄_0 ψ_x⟩` (translation invariance, `PtCorr.avg_psibar_psi_transl`).

## Proof
* `avg_one_decomp`: the correlation bridge `⟨ψ̄_aψ_b⟩ = ε(Z̃^obs_ab)/(l₀²(1+ũ))`
  (`avg_one_eq'`) and the component formula `ε_ZtO_ab_one`:
  `⟨ψ̄_aψ_b⟩ = q_N/l₀² + ((λ_{a,N}λ_{b,N} - (r_a + r_b)) τ + k_ab)/l₀² / (1+ũ)`.
* `qN_sub_le_one`: `‖q_N - l₀² ∑_k C_{k+1}(a,b)‖ ≤ (…) ℓ_{j_ab}² θ^{j_ab}` from
  `Obs.Vobs_recursion_one` summed (`PtCorr.qsum_one_bound`), `r_{x,k} = 0` for `k ≤ j_ab` and
  `|r_{x,k}| ≤ C e θ^{j_ab}` (`Obs.Vobs_bd`), and `‖λ_{x,k} - l₀‖ ≤ C l₀ b₀ θ^k` (`lamOne_of`).
  `∑_k C_{k+1}(a,b) = W_N(b - a)` (`sum_covAt_eq_WN`).
* `E₁ = q_N/l₀² - W`, `E₂ = ((λ_aλ_b - l₀²) τ - (r_a+r_b) τ + k_ab)/l₀²` (`norm_E2_one_le`):
  `|λ_aλ_b - l₀²| ≤ C l₀² b₀ θ^N`, `θ^N ≤ r^{-κ}`, `θ^{j_ab} ≤ L^κ r^{-κ}`,
  `ℓ_{j_ab}² θ^{j_ab} ≤ ℓ₀² L^{d-2+κ} r^{-(d-2+κ)}` (`PtCorr.Conv`), `|τ| ≤ 1/(m²|Λ|)`,
  `|k_ab| ≤ (ℓ_N² + |τ|) ‖K^obs_N‖`, `ℓ_N² θ^N = ℓ₀² L^{-(d-2+κ)N}`.
* We fix `l₀ = λ̄` (the correlation functions do not depend on `l₀`) and `b̄ = λ̄`.

## Deviations
* **Constant term.** The extra `L^{-(d-2+κ)N}` in `E₂` is the constant part
  `ε(K^{ab}_N(Λ))` of `k_ab` (omitted in the paper), `|·| ≤ ℓ_N² ‖K^obs_N‖`.
* The paper writes `|a - b| ≤ L` in the proof; we use `L^{j_ab} ≤ 2|a-b| < L^{j_ab+1}`.
* `λ_∞ = λ₀` (paper, via `N → ∞`) is replaced by the finite-`N` bound of `lamOne_of`.
* `m² > 0` and `1 + ũ ≠ 0` are hypotheses; the errors are placed as in the paper
  (`E₂` inside `1/(1+ũ)`).
-/

namespace PtCorr

noncomputable section

open Finset Grassmann Obs Loc Step Flow SA FRD

variable {d L : ℕ} [NeZero L]

section Decomp

variable {N : ℕ} (V₀ : Vcoup) (l₀ : ℂ) (a b : Lam d L N) {msq ℓ₀ : ℝ}

/-- `⟨ψ̄_aψ_b⟩ = q_N/l₀² + ((λ_{a,N}λ_{b,N} - (r_{a,N}+r_{b,N})) τ + k_ab)/l₀² / (1+ũ)`. -/
theorem avg_one_decomp (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j))
    (hl : l₀ ≠ 0) (hu : 1 + Suscept.utN d L N msq V₀ ≠ 0) :
    avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar a * psi b) =
      qN d L .one N msq V₀ (initObs .one l₀) a b / l₀ ^ 2 +
        (((laOf .one (Vo1 d L N msq V₀ l₀ a b) * lbOf .one (Vo1 d L N msq V₀ l₀ a b) -
            (raOf .one (Vo1 d L N msq V₀ l₀ a b) + rbOf .one (Vo1 d L N msq V₀ l₀ a b))) *
            tau d L N msq + kabOne d L N msq V₀ (initObs .one l₀) a b) / l₀ ^ 2) /
          (1 + Suscept.utN d L N msq V₀) := by
  have h1 := avg_one_eq' hd hL hN hmsq hgood V₀ hl a b
  have h2 := ε_ZtO_ab_one V₀ l₀ a b hd hL hN hmsq hgood
  have h2' : ε (((eu d L N msq V₀ • Gobs d L .one N msq V₀ l₀ a b : OE .one (Lam d L N))) :
        SA .one (Lam d L N)).ab =
      qN d L .one N msq V₀ (initObs .one l₀) a b * (1 + Suscept.utN d L N msq V₀) +
        (laOf .one (Vo1 d L N msq V₀ l₀ a b) * lbOf .one (Vo1 d L N msq V₀ l₀ a b) -
          (raOf .one (Vo1 d L N msq V₀ l₀ a b) + rbOf .one (Vo1 d L N msq V₀ l₀ a b))) *
          tau d L N msq +
        kabOne d L N msq V₀ (initObs .one l₀) a b := h2
  rw [h1, h2']
  have hl2 : l₀ ^ 2 ≠ 0 := pow_ne_zero 2 hl
  field_simp
  ring

end Decomp

/-- **The sum of the `q` increments** (Case (1)): with `‖K^obs_k‖_k ≤ e θ^k` and
`‖λ_{x,k} - l₀‖ ≤ Λ θ^k` (`x = a, b`, `k ≤ N`):
`‖q_N - l₀² ∑_{k<N} C_{k+1}(a,b)‖ ≤ (4 C_r e + 2(Λ(|l₀|+Λ) + |l₀|Λ) + 4 C_b e/(1-θ))
ℓ_{j_ab}² θ^{j_ab}`, and `|r_{x,j}| ≤ C_b e θ^{j_ab}/(1-θ)` for `j ≤ N`. -/
theorem qN_sub_le_one (hd : 3 ≤ d) : ∃ Cr Cb : ℝ, 0 ≤ Cr ∧ 0 ≤ Cb ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) ≤ L → ∀ (N : ℕ) (msq : ℝ) (V₀ : Vcoup) (ℓ₀ : ℝ),
    0 < ℓ₀ → (∀ k < N, GoodCov (d := d) (L := L) (N := N) k ℓ₀ (Flow.covAt d L N msq k)) →
    ∀ (l₀ : ℂ) (a b : Lam d L N) (A : ℝ), 1 ≤ A → ∀ {e θ Λ : ℝ}, 0 ≤ e → 0 ≤ θ → θ < 1 →
    0 ≤ Λ →
    (∀ k < N, KnormObs .one ℓ₀ a b k A (flowO d L .one N msq V₀ (initObs .one l₀) a b k).2 ≤
      ENNReal.ofReal (e * θ ^ k)) →
    (∀ k ≤ N, ‖laOne d L N msq V₀ l₀ a b k - l₀‖ ≤ Λ * θ ^ k) →
    (∀ k ≤ N, ‖lbOne d L N msq V₀ l₀ a b k - l₀‖ ≤ Λ * θ ^ k) →
    ‖qN d L .one N msq V₀ (initObs .one l₀) a b -
        l₀ ^ 2 * ∑ k ∈ range N, (Flow.covAt d L N msq k a b : ℂ)‖ ≤
      (4 * Cr * e + 2 * (Λ * (‖l₀‖ + Λ) + ‖l₀‖ * Λ) + 4 * (Cb * e / (1 - θ))) *
        (ellj d L ℓ₀ (coal L a b) ^ 2 * θ ^ coal L a b) ∧
    ∀ j ≤ N,
      ‖raOf .one (flowO d L .one N msq V₀ (initObs .one l₀) a b j).1‖ ≤
          Cb * e * θ ^ coal L a b / (1 - θ) ∧
        ‖rbOf .one (flowO d L .one N msq V₀ (initObs .one l₀) a b j).1‖ ≤
          Cb * e * θ ^ coal L a b / (1 - θ) := by
  obtain ⟨Cr, hCr, hrec⟩ := Vobs_recursion_one d
  obtain ⟨Cb, hCb, hbd⟩ := Vobs_bd hd
  refine ⟨Cr, Cb, hCr, hCb, ?_⟩
  intro L _ hL N msq V₀ ℓ₀ hℓ₀ hC l₀ a b A hA e θ Λ he hθ0 hθ1 hΛ hK hla hlb
  have hd1 : 1 ≤ d := by omega
  have hL2 : 2 ≤ L := le_trans (by
      have : 2 ^ 1 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this) hL
  have hr : ∀ j ≤ N,
      (‖raOf .one (flowO d L .one N msq V₀ (initObs .one l₀) a b j).1‖ ≤
          Cb * e * θ ^ coal L a b / (1 - θ) ∧
        ‖rbOf .one (flowO d L .one N msq V₀ (initObs .one l₀) a b j).1‖ ≤
          Cb * e * θ ^ coal L a b / (1 - θ)) ∧
      (j ≤ coal L a b → raOf .one (flowO d L .one N msq V₀ (initObs .one l₀) a b j).1 = 0 ∧
        rbOf .one (flowO d L .one N msq V₀ (initObs .one l₀) a b j).1 = 0) := by
    intro j hj
    obtain ⟨-, -, h3, h4, h5, -⟩ := hbd L hL N msq V₀ ℓ₀ hℓ₀ hC .one l₀ a b A hA θ e hθ0 hθ1 he
      j hj (fun k hk => hK k (by omega))
    have hs : sab .one (ellj d L ℓ₀ (coal L a b)) = 1 := rfl
    rw [hs, mul_one] at h3 h4
    exact ⟨⟨h3, h4⟩, h5⟩
  refine ⟨?_, fun j hj => (hr j hj).1⟩
  have hq := qsum_one_bound hd hL2 hℓ₀ hC a b hθ0 hθ1.le he hCr hΛ l₀
    (fun k => laOne d L N msq V₀ l₀ a b k) (fun k => lbOne d L N msq V₀ l₀ a b k)
    (fun k => raOf .one (flowO d L .one N msq V₀ (initObs .one l₀) a b k).1)
    (fun k => rbOf .one (flowO d L .one N msq V₀ (initObs .one l₀) a b k).1)
    (fun k => qaOf .one (nextAt d L .one N msq V₀ (initObs .one l₀) a b k) +
      qbOf .one (nextAt d L .one N msq V₀ (initObs .one l₀) a b k))
    hla hlb (fun k hk => ⟨(hr k hk).1.1, fun h => ((hr k hk).2 h).1⟩)
    (fun k hk => ⟨(hr k hk).1.2, fun h => ((hr k hk).2 h).2⟩)
    (fun k hk => (hrec L N k ℓ₀ hℓ₀ (Flow.covAt d L N msq k)
      (flowO d L .one N msq V₀ (initObs .one l₀) a b k).1
      (flowO d L .one N msq V₀ (initObs .one l₀) a b k).2 a b A hA (e * θ ^ k) (by positivity)
      (hK k hk) (fun hlt Y hY => abSmall_flowO V₀ l₀ a b hd1 hL hC hk hlt hY)).2.2.1)
  have eq : qN d L .one N msq V₀ (initObs .one l₀) a b =
      ∑ k ∈ range N, (qaOf .one (nextAt d L .one N msq V₀ (initObs .one l₀) a b k) +
        qbOf .one (nextAt d L .one N msq V₀ (initObs .one l₀) a b k)) := rfl
  rw [eq]
  refine hq.trans (le_of_eq ?_)
  ring

/-- `E₂ = ((λ_aλ_b - (r_a + r_b)) τ + k)/l₀² - τ` is bounded by
`((|λ_aλ_b - l₀²| + |r_a| + |r_b|) |τ| + |k|)/|l₀|²`. -/
theorem norm_E2_one_le (l₀ la lb ra rb τ k : ℂ) (hl : l₀ ≠ 0) :
    ‖((la * lb - (ra + rb)) * τ + k) / l₀ ^ 2 - τ‖ ≤
      ((‖la * lb - l₀ ^ 2‖ + (‖ra‖ + ‖rb‖)) * ‖τ‖ + ‖k‖) / ‖l₀‖ ^ 2 := by
  have hl2 : l₀ ^ 2 ≠ 0 := pow_ne_zero 2 hl
  have e : ((la * lb - (ra + rb)) * τ + k) / l₀ ^ 2 - τ =
      ((la * lb - l₀ ^ 2) * τ - (ra + rb) * τ + k) / l₀ ^ 2 := by
    field_simp; ring
  rw [e, norm_div, norm_pow]
  have hpos : 0 < ‖l₀‖ ^ 2 := by positivity
  refine div_le_div_of_nonneg_right ?_ hpos.le
  calc ‖(la * lb - l₀ ^ 2) * τ - (ra + rb) * τ + k‖
      ≤ ‖(la * lb - l₀ ^ 2) * τ‖ + ‖(ra + rb) * τ‖ + ‖k‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by
        rw [norm_mul, norm_mul]
        have := norm_add_le ra rb
        have := norm_nonneg τ
        nlinarith

/-! ### Real-number bookkeeping (abstract atoms, to keep elaboration cheap) -/

/-- `E₁ = q/l₀² - W`: from `‖q - l₀² W‖ ≤ (4C_r e + 2(Λ(|l₀|+Λ)+|l₀|Λ) + 4C_b e/(1-θ)) P`,
`e = C_f λ̄ β`, `Λ = C_l λ̄ β`, `|l₀| = λ̄`, `β ≤ λ̄`, `P ≤ B`. -/
theorem E1_one_aux {q l₀ W : ℂ} {lbar β Cr Cf Cb Cl θ P B : ℝ} (hlbar : 0 < lbar)
    (hl0 : ‖l₀‖ = lbar) (hβ0 : 0 ≤ β) (hβ : β ≤ lbar) (hCr : 0 ≤ Cr) (hCf : 0 ≤ Cf)
    (hCb : 0 ≤ Cb) (hCl : 0 ≤ Cl) (hθ : θ < 1) (hP0 : 0 ≤ P) (hPB : P ≤ B)
    (hq : ‖q - l₀ ^ 2 * W‖ ≤
      (4 * Cr * (Cf * lbar * β) + 2 * (Cl * lbar * β * (‖l₀‖ + Cl * lbar * β) +
        ‖l₀‖ * (Cl * lbar * β)) + 4 * (Cb * (Cf * lbar * β) / (1 - θ))) * P) :
    ‖q / l₀ ^ 2 - W‖ ≤
      (4 * Cr * Cf / lbar + 2 * Cl * (2 + Cl * lbar) + 4 * Cb * Cf / (lbar * (1 - θ))) * B * β := by
  have hl0ne : l₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hl0; exact hlbar.ne' hl0.symm
  have h1θ : 0 < 1 - θ := by linarith
  have e1 : q / l₀ ^ 2 - W = (q - l₀ ^ 2 * W) / l₀ ^ 2 := by field_simp
  rw [e1, norm_div, norm_pow, hl0]
  rw [hl0] at hq
  set K₁ := 4 * Cr * Cf / lbar + 2 * Cl * (2 + Cl * lbar) + 4 * Cb * Cf / (lbar * (1 - θ))
    with hK₁
  have hcoef : 4 * Cr * (Cf * lbar * β) + 2 * (Cl * lbar * β * (lbar + Cl * lbar * β) +
        lbar * (Cl * lbar * β)) + 4 * (Cb * (Cf * lbar * β) / (1 - θ)) ≤ lbar ^ 2 * β * K₁ := by
    have h : lbar ^ 2 * β * K₁ - (4 * Cr * (Cf * lbar * β) + 2 * (Cl * lbar * β *
        (lbar + Cl * lbar * β) + lbar * (Cl * lbar * β)) + 4 * (Cb * (Cf * lbar * β) / (1 - θ))) =
        2 * lbar ^ 2 * β * Cl ^ 2 * (lbar - β) := by
      rw [hK₁]; field_simp; ring
    have : 0 ≤ 2 * lbar ^ 2 * β * Cl ^ 2 * (lbar - β) := by
      have : 0 ≤ lbar - β := by linarith
      positivity
    linarith
  have hK₁0 : 0 ≤ K₁ := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc ‖q - l₀ ^ 2 * W‖ ≤ lbar ^ 2 * β * K₁ * P := hq.trans (mul_le_mul_of_nonneg_right hcoef hP0)
    _ ≤ lbar ^ 2 * β * K₁ * B := mul_le_mul_of_nonneg_left hPB (by positivity)
    _ = K₁ * B * β * lbar ^ 2 := by ring

/-- `E₂ = ((λ_aλ_b - (r_a+r_b)) τ + k)/l₀² - τ`, with `e = C_f λ̄ β`, `Λ = C_l λ̄ β`,
`|λ_aλ_b - l₀²| ≤ (Λ(|l₀|+Λ)+|l₀|Λ) t_N`, `t_N ≤ t₁`, `|r_x| ≤ C_b e t_ab/(1-θ)`,
`t_ab ≤ L_κ t₁`, `|k| ≤ (ℓ_N² + |τ|) e t_N`, `ℓ_N² t_N = ℓ₀² Q`, `|τ| ≤ T`. -/
theorem E2_one_aux {l₀ la lb ra rb τ k : ℂ}
    {lbar β Cf Cl Cb Lk ℓ₀ t1 tN tab T Q ℓN2 θ : ℝ} (hlbar : 0 < lbar) (hl0 : ‖l₀‖ = lbar)
    (hβ0 : 0 ≤ β) (hβ : β ≤ lbar) (hCf : 0 ≤ Cf) (hCl : 0 ≤ Cl) (hCb : 0 ≤ Cb) (hLk : 0 ≤ Lk)
    (ht1 : 0 ≤ t1) (hT : 0 ≤ T) (_hQ : 0 ≤ Q) (hθ : θ < 1) (htN0 : 0 ≤ tN) (htN : tN ≤ t1)
    (_htab0 : 0 ≤ tab) (htab : tab ≤ Lk * t1)
    (hμ : ‖la * lb - l₀ * l₀‖ ≤
      (Cl * lbar * β * (‖l₀‖ + Cl * lbar * β) + ‖l₀‖ * (Cl * lbar * β)) * tN)
    (hra : ‖ra‖ ≤ Cb * (Cf * lbar * β) * tab / (1 - θ))
    (hrb : ‖rb‖ ≤ Cb * (Cf * lbar * β) * tab / (1 - θ))
    (hτ : ‖τ‖ ≤ T) (hk : ‖k‖ ≤ (ℓN2 + ‖τ‖) * (Cf * lbar * β * tN)) (hℓN : ℓN2 * tN = ℓ₀ ^ 2 * Q) :
    ‖((la * lb - (ra + rb)) * τ + k) / l₀ ^ 2 - τ‖ ≤
      β * ((Cl * (2 + Cl * lbar) + 2 * Cb * Cf * Lk / (lbar * (1 - θ)) + Cf / lbar) * (t1 * T) +
        (Cf * ℓ₀ ^ 2 / lbar) * Q) := by
  have hl0ne : l₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hl0; exact hlbar.ne' hl0.symm
  have h1θ : 0 < 1 - θ := by linarith
  have h2 := norm_E2_one_le l₀ la lb ra rb τ k hl0ne
  rw [hl0] at h2 hμ
  refine h2.trans ?_
  rw [div_le_iff₀ (by positivity)]
  set e := Cf * lbar * β with he
  set Λ := Cl * lbar * β with hΛ
  have he0 : 0 ≤ e := by positivity
  have hΛ0 : 0 ≤ Λ := by positivity
  set M := (Λ * (lbar + Λ) + lbar * Λ) * t1 with hM
  set S := Cb * e * (Lk * t1) / (1 - θ) with hS
  have hμ' : ‖la * lb - l₀ ^ 2‖ ≤ M := by
    rw [sq]; exact hμ.trans (mul_le_mul_of_nonneg_left htN (by positivity))
  have hra' : ‖ra‖ ≤ S := hra.trans (by rw [hS]; gcongr)
  have hrb' : ‖rb‖ ≤ S := hrb.trans (by rw [hS]; gcongr)
  have hk' : ‖k‖ ≤ e * ℓ₀ ^ 2 * Q + T * (e * t1) := by
    refine hk.trans ?_
    have h3 : (ℓN2 + ‖τ‖) * (e * tN) = e * (ℓN2 * tN) + ‖τ‖ * (e * tN) := by ring
    rw [h3, hℓN]
    have : ‖τ‖ * (e * tN) ≤ T * (e * t1) := by gcongr
    linarith
  have h3 : ‖la * lb - l₀ ^ 2‖ + (‖ra‖ + ‖rb‖) ≤ M + (S + S) :=
    add_le_add hμ' (add_le_add hra' hrb')
  have hM0 : 0 ≤ M := by positivity
  have hS0 : 0 ≤ S := by positivity
  have h4 := mul_le_mul h3 hτ (norm_nonneg _) (by positivity)
  have hfin : β * ((Cl * (2 + Cl * lbar) + 2 * Cb * Cf * Lk / (lbar * (1 - θ)) + Cf / lbar) *
        (t1 * T) + (Cf * ℓ₀ ^ 2 / lbar) * Q) * lbar ^ 2 -
      ((M + (S + S)) * T + (e * ℓ₀ ^ 2 * Q + T * (e * t1))) =
      lbar ^ 2 * β * Cl ^ 2 * (lbar - β) * t1 * T := by
    rw [hM, hS, he, hΛ]; field_simp; ring
  have hfin0 : 0 ≤ lbar ^ 2 * β * Cl ^ 2 * (lbar - β) * t1 * T := by
    have : 0 ≤ lbar - β := by linarith
    positivity
  linarith

/-! ### The core estimate for general `a ≠ b` -/

section Core

variable {N : ℕ} (V₀ : Vcoup) (a b : Lam d L N)

/-- **Core of `lem:2pt` Case (1)**, for a given flow: with `θ = L^{-κ}`, `e = C_f λ̄ β`,
`Λ = C_l λ̄ β` (`β = |b₀|`), the flow facts `‖K^obs_N‖ ≤ e θ^N`, `|λ_{x,N} - λ̄| ≤ Λ θ^N`, the
`q`-sum bound and the `r` bounds (from `qN_sub_le_one`), and `r = |a - b|_∞`:
`⟨ψ̄_aψ_b⟩ = W_N(b-a) + (τ + E₂)/(1+ũ) + E₁`, `|E₁| ≤ K₁ ℓ₀² L^{d-2+κ} β r^{-(d-2+κ)}`,
`|E₂| ≤ β (K₂ r^{-κ}/(m²|Λ|) + K₃ L^{-(d-2+κ)N})` with explicit `K₁, K₂, K₃`. -/
theorem two_pt_one_core (hd : 3 ≤ d) (hL8 : 2 ^ (d + 3) ≤ L) (hN : 1 ≤ N) {msq ℓ₀ A : ℝ}
    (hmsq : 0 < msq) (hℓ₀ : 0 < ℓ₀) (hA : 1 ≤ A)
    (hgood : ∀ k < N, GoodCov (d := d) (L := L) (N := N) k ℓ₀ (Flow.covAt d L N msq k))
    {lbar β Cf Cl Cr Cb κ θ : ℝ} (hlbar : 0 < lbar) (hβ0 : 0 ≤ β) (hβ : β ≤ lbar)
    (hCf : 0 ≤ Cf) (hCl : 0 ≤ Cl) (hCr : 0 ≤ Cr) (hCb : 0 ≤ Cb) (hκ : 0 < κ)
    (hθ : θ = (L : ℝ) ^ (-κ)) (hab : a ≠ b) (hu : 1 + Suscept.utN d L N msq V₀ ≠ 0)
    (hK : KnormObs .one ℓ₀ a b N A
        (flowO d L .one N msq V₀ (initObs .one (lbar : ℂ)) a b N).2 ≤
      ENNReal.ofReal (Cf * lbar * β * θ ^ N))
    (hla : ‖laOne d L N msq V₀ (lbar : ℂ) a b N - (lbar : ℂ)‖ ≤ Cl * lbar * β * θ ^ N)
    (hlb : ‖lbOne d L N msq V₀ (lbar : ℂ) a b N - (lbar : ℂ)‖ ≤ Cl * lbar * β * θ ^ N)
    (hq : ‖qN d L .one N msq V₀ (initObs .one (lbar : ℂ)) a b -
        (lbar : ℂ) ^ 2 * ∑ k ∈ range N, (Flow.covAt d L N msq k a b : ℂ)‖ ≤
      (4 * Cr * (Cf * lbar * β) + 2 * (Cl * lbar * β * (‖(lbar : ℂ)‖ + Cl * lbar * β) +
        ‖(lbar : ℂ)‖ * (Cl * lbar * β)) + 4 * (Cb * (Cf * lbar * β) / (1 - θ))) *
        (ellj d L ℓ₀ (coal L a b) ^ 2 * θ ^ coal L a b))
    (hra : ‖raOf .one (flowO d L .one N msq V₀ (initObs .one (lbar : ℂ)) a b N).1‖ ≤
      Cb * (Cf * lbar * β) * θ ^ coal L a b / (1 - θ))
    (hrb : ‖rbOf .one (flowO d L .one N msq V₀ (initObs .one (lbar : ℂ)) a b N).1‖ ≤
      Cb * (Cf * lbar * β) * θ ^ coal L a b / (1 - θ)) :
    ∃ E₁ E₂ : ℂ,
      ‖E₁‖ ≤ (4 * Cr * Cf / lbar + 2 * Cl * (2 + Cl * lbar) + 4 * Cb * Cf / (lbar * (1 - θ))) *
          (ℓ₀ ^ 2 * (L : ℝ) ^ ((d : ℝ) - 2 + κ)) * β *
          (supNorm (a - b) : ℝ) ^ (-((d : ℝ) - 2 + κ)) ∧
      ‖E₂‖ ≤ β * ((Cl * (2 + Cl * lbar) + 2 * Cb * Cf * (L : ℝ) ^ κ / (lbar * (1 - θ)) +
            Cf / lbar) * ((supNorm (a - b) : ℝ) ^ (-κ) / (msq * Fintype.card (Lam d L N))) +
          (Cf * ℓ₀ ^ 2 / lbar) * (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N))) ∧
      avg (Suscept.Cov d L N msq) (VE V₀ univ) (psibar a * psi b) =
        (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (b - a) : ℂ) +
          (tau d L N msq + E₂) / (1 + Suscept.utN d L N msq V₀) + E₁ := by
  have hd1 : 1 ≤ d := by omega
  have hL2 : 2 ≤ L := le_trans (by
      have : 2 ^ 1 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this) hL8
  have hLr1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨hθ0, hθ1⟩ := theta_one hLr1 hκ
  rw [← hθ] at hθ0 hθ1
  have hl0 : ‖(lbar : ℂ)‖ = lbar := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlbar]
  have hl0ne : (lbar : ℂ) ≠ 0 := by exact_mod_cast hlbar.ne'
  obtain ⟨-, -, hkab⟩ := kOne_bounds hℓ₀ hA (by positivity : 0 ≤ Cf * lbar * β * θ ^ N)
    (initObs .one (lbar : ℂ)) hK
  have hsumW : ∑ k ∈ range N, (Flow.covAt d L N msq k a b : ℂ) =
      ((WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (b - a) : ℝ) : ℂ) := by
    rw [← sum_covAt_eq_WN hmsq hN a b, Complex.ofReal_sum]
  rw [hsumW] at hq
  have hdec := avg_one_decomp V₀ (lbar : ℂ) a b hd1 hL8 hN hmsq hgood hl0ne hu
  -- conversions
  have hPB : ellj d L ℓ₀ (coal L a b) ^ 2 * θ ^ coal L a b ≤
      ℓ₀ ^ 2 * ((L : ℝ) ^ ((d : ℝ) - 2 + κ) * (supNorm (a - b) : ℝ) ^ (-((d : ℝ) - 2 + κ))) := by
    rw [hθ]; exact ellj_coal_sq_mul_pow_le (by omega) hL2 ℓ₀ hκ.le hab
  have hθab : θ ^ coal L a b ≤ (L : ℝ) ^ κ * (supNorm (a - b) : ℝ) ^ (-κ) := by
    rw [hθ]; exact pow_coal_le hL2 hκ.le hab
  have hθN : θ ^ N ≤ (supNorm (a - b) : ℝ) ^ (-κ) := by
    rw [hθ]; exact pow_N_le hκ.le hab
  have hn0 : (0 : ℝ) < Fintype.card (Lam d L N) := card_pos'
  have hτ : ‖tau d L N msq‖ ≤ 1 / (msq * Fintype.card (Lam d L N)) := by
    obtain ⟨ht0, ht1⟩ := tNN_nonneg_le (d := d) hd1 hmsq L N
    rw [tau, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht0 hn0.le)]
    rw [div_le_div_iff₀ hn0 (by positivity)]
    have : Suscept.tNN d L N msq * msq ≤ 1 := by rwa [le_div_iff₀ hmsq] at ht1
    nlinarith
  have hℓN : ellj d L ℓ₀ N ^ 2 * θ ^ N = ℓ₀ ^ 2 * (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) := by
    rw [Obs.ellj_sq, rpow_neg_mul_nat hL0.le, mul_assoc, hθ, pow_mul_pow_rpow hL0]
  have hμ := norm_mul_sub_mul_le_pow (by positivity : 0 ≤ Cl * lbar * β)
    (by positivity : 0 ≤ Cl * lbar * β) (by positivity : 0 ≤ θ ^ N) (pow_le_one₀ hθ0 hθ1.le)
    hla hlb
  refine ⟨qN d L .one N msq V₀ (initObs .one (lbar : ℂ)) a b / (lbar : ℂ) ^ 2 -
      ((WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N (b - a) : ℝ) : ℂ),
    ((laOf .one (Vo1 d L N msq V₀ (lbar : ℂ) a b) * lbOf .one (Vo1 d L N msq V₀ (lbar : ℂ) a b) -
        (raOf .one (Vo1 d L N msq V₀ (lbar : ℂ) a b) +
          rbOf .one (Vo1 d L N msq V₀ (lbar : ℂ) a b))) * tau d L N msq +
        kabOne d L N msq V₀ (initObs .one (lbar : ℂ)) a b) / (lbar : ℂ) ^ 2 - tau d L N msq,
    ?_, ?_, ?_⟩
  · exact (E1_one_aux hlbar hl0 hβ0 hβ hCr hCf hCb hCl hθ1 (by positivity) hPB hq).trans
      (le_of_eq (by ring))
  · have h := E2_one_aux (Lk := (L : ℝ) ^ κ) (T := 1 / (msq * Fintype.card (Lam d L N)))
      (t1 := (supNorm (a - b) : ℝ) ^ (-κ)) (Q := (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)))
      hlbar hl0 hβ0 hβ hCf hCl hCb (by positivity) (by positivity) (by positivity)
      (by positivity) hθ1 (by positivity) hθN (by positivity) hθab hμ hra hrb hτ hkab hℓN
    refine h.trans (le_of_eq ?_)
    rw [div_eq_mul_one_div ((supNorm (a - b) : ℝ) ^ (-κ))]
  · rw [hdec]
    field_simp
    ring

end Core

/-- **Lemma `lem:2pt`, Case (1), for a given flow** `V₀c` with `FlowData` (`e:2pt-a`,
Tier 1; see `lem_2pt_one`). The flow is run with `l₀ = λ̄`. -/
theorem lem_2pt_one_of (hd : 3 ≤ d) {L : ℕ} [NeZero L] {A ℓ₀ lbar Cf κ : ℝ}
    {V₀c : ℝ → ℂ → Vcoup} (HF : FlowData d L A ℓ₀ V₀c lbar Cf κ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (msq : ℝ), 0 < msq → ∀ (b₀ : ℂ), ‖b₀‖ ≤ lbar →
      ∀ x : Lam d L N, x ≠ 0 → 1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 →
      ∃ E₁ E₂ : ℂ,
        ‖E₁‖ ≤ C * ‖b₀‖ * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ)) ∧
        ‖E₂‖ ≤ C * ‖b₀‖ * ((supNorm x : ℝ) ^ (-κ) / (msq * Fintype.card (Lam d L N)) +
          (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N))) ∧
        avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
            (psibar (ctr d L N) * psi (ctr d L N + x)) =
          (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) +
            (tau d L N msq + E₂) / (1 + Suscept.utN d L N msq (V₀c msq b₀)) + E₁ ∧
        avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ) (psibar 0 * psi x) =
          (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) +
            (tau d L N msq + E₂) / (1 + Suscept.utN d L N msq (V₀c msq b₀)) + E₁ := by
  obtain ⟨Cr, Cb, hCr, hCb, hqN⟩ := qN_sub_le_one hd
  obtain ⟨Cl, hCl, hlam⟩ := lamOne_of hd HF
  have hℓ₀ := HF.hℓ₀
  have hlbar := HF.lbar_pos
  have hCf := HF.C_nonneg
  have hκ := HF.κ_pos
  have hL8 := HF.hL8
  have hA1 := HF.hA1
  have hgood := HF.good
  have hobs := HF.obs
  have hL2 : 2 ≤ L := le_trans (by
      have : 2 ^ 1 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this) hL8
  have hLr1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (L : ℝ) ^ (-κ) := ⟨_, rfl⟩
  obtain ⟨hθ0, hθ1⟩ := theta_one hLr1 hκ
  rw [← hθ] at hθ0 hθ1
  have h1θ : 0 < 1 - θ := by linarith
  have hpow : ∀ k : ℕ, (L : ℝ) ^ (-(κ * k)) = θ ^ k := fun k => by
    rw [hθ]; exact rpow_neg_mul_nat hL0.le κ k
  obtain ⟨CE, hCE⟩ : ∃ CE : ℝ, CE = (4 * Cr * Cf / lbar + 2 * Cl * (2 + Cl * lbar) +
      4 * Cb * Cf / (lbar * (1 - θ))) * (ℓ₀ ^ 2 * (L : ℝ) ^ ((d : ℝ) - 2 + κ)) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = Cl * (2 + Cl * lbar) +
      2 * Cb * Cf * (L : ℝ) ^ κ / (lbar * (1 - θ)) + Cf / lbar := ⟨_, rfl⟩
  obtain ⟨K₃, hK₃⟩ : ∃ K₃ : ℝ, K₃ = Cf * ℓ₀ ^ 2 / lbar := ⟨_, rfl⟩
  have hCE0 : 0 ≤ CE := by rw [hCE]; positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hK₃0 : 0 ≤ K₃ := by rw [hK₃]; positivity
  refine ⟨CE + K₂ + K₃, by positivity, ?_⟩
  intro N hN msq hmsq b₀ hb₀ x hx hu
  have hl0 : ‖(lbar : ℂ)‖ = lbar := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlbar]
  have hne : ctr d L N + x ≠ ctr d L N := by
    intro h; apply hx
    simpa using congrArg (fun y => y - ctr d L N) h
  have hab : ctr d L N ≠ ctr d L N + x := fun h => hne h.symm
  have hr : supNorm (ctr d L N - (ctr d L N + x)) = supNorm x := by
    rw [sub_add_cancel_left, supNorm_neg]
  have hbl : ‖b₀‖ ≤ ‖(lbar : ℂ)‖ := by rw [hl0]; exact hb₀
  have hll : ‖(lbar : ℂ)‖ ≤ lbar := hl0.le
  have hK : ∀ k ≤ N, KnormObs .one ℓ₀ (ctr d L N) (ctr d L N + x) k A
      (flowO d L .one N msq (V₀c msq b₀) (initObs .one (lbar : ℂ)) (ctr d L N)
        (ctr d L N + x) k).2 ≤ ENNReal.ofReal (Cf * lbar * ‖b₀‖ * θ ^ k) := by
    intro k hk
    have := (hobs .one N msq (lbar : ℂ) b₀ (ctr d L N + x) hmsq.le hbl hll hne k hk).2
    rwa [hpow k, hl0] at this
  have hla : ∀ k ≤ N, ‖laOne d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + x) k -
      (lbar : ℂ)‖ ≤ Cl * lbar * ‖b₀‖ * θ ^ k := by
    intro k hk
    have := (hlam N msq (lbar : ℂ) b₀ (ctr d L N + x) hmsq hbl hll hne k hk).1
    rwa [hpow k, hl0] at this
  have hlb : ∀ k ≤ N, ‖lbOne d L N msq (V₀c msq b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + x) k -
      (lbar : ℂ)‖ ≤ Cl * lbar * ‖b₀‖ * θ ^ k := by
    intro k hk
    have := (hlam N msq (lbar : ℂ) b₀ (ctr d L N + x) hmsq hbl hll hne k hk).2
    rwa [hpow k, hl0] at this
  obtain ⟨hq, hrab⟩ := hqN L hL8 N msq (V₀c msq b₀) ℓ₀ hℓ₀ (hgood N msq hmsq.le) (lbar : ℂ)
    (ctr d L N) (ctr d L N + x) A hA1 (e := Cf * lbar * ‖b₀‖) (θ := θ)
    (Λ := Cl * lbar * ‖b₀‖) (by positivity) hθ0 hθ1 (by positivity)
    (fun k hk => by have := hK k hk.le; rwa [mul_assoc (Cf * lbar)] at this ⊢) hla hlb
  obtain ⟨hra, hrb⟩ := hrab N le_rfl
  obtain ⟨E₁, E₂, h1, h2, h3⟩ := two_pt_one_core (V₀c msq b₀) (ctr d L N) (ctr d L N + x)
    hd hL8 hN hmsq hℓ₀ hA1 (hgood N msq hmsq.le) hlbar (norm_nonneg b₀) hb₀ hCf hCl hCr hCb hκ
    hθ hab hu (hK N le_rfl) (hla N le_rfl) (hlb N le_rfl) hq hra hrb
  rw [hr, add_sub_cancel_left] at *
  refine ⟨E₁, E₂, ?_, ?_, h3, ?_⟩
  · rw [← hCE] at h1
    refine h1.trans ?_
    have : 0 ≤ ‖b₀‖ * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ)) := by positivity
    calc CE * ‖b₀‖ * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))
        = CE * (‖b₀‖ * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))) := by ring
      _ ≤ (CE + K₂ + K₃) * (‖b₀‖ * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ))) :=
          mul_le_mul_of_nonneg_right (by linarith) this
      _ = _ := by ring
  · rw [← hK₂, ← hK₃] at h2
    refine h2.trans ?_
    have hA' : 0 ≤ (supNorm x : ℝ) ^ (-κ) / (msq * Fintype.card (Lam d L N)) := by positivity
    have hB' : 0 ≤ (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) := by positivity
    have hb0 := norm_nonneg b₀
    calc ‖b₀‖ * (K₂ * ((supNorm x : ℝ) ^ (-κ) / (msq * Fintype.card (Lam d L N))) +
          K₃ * (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)))
        ≤ ‖b₀‖ * ((CE + K₂ + K₃) * ((supNorm x : ℝ) ^ (-κ) / (msq * Fintype.card (Lam d L N))) +
          (CE + K₂ + K₃) * (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N))) := by
          gcongr <;> linarith
      _ = _ := by ring
  · have ht := avg_psibar_psi_transl hmsq hN (V₀c msq b₀) (ctr d L N) 0 x
    rw [zero_add, add_comm x] at ht
    rw [← ht]
    exact h3

/-- **Lemma `lem:2pt`, Case (1)** (`e:2pt-a`, Tier 1: finite `N`, `m² > 0`, couplings of
scale `N`), for `a = ctr`, `b = ctr + x`, `x ≠ 0`, `r = |x|_∞`, `W = W_N(x)`:
`⟨ψ̄_aψ_b⟩ = W + (τ + E₂)/(1+ũ) + E₁` with `|E₁| ≤ C|b₀| r^{-(d-2+κ)}` and
`|E₂| ≤ C|b₀|(r^{-κ}/(m²|Λ|) + L^{-(d-2+κ)N})`; the same `E₁, E₂` for `⟨ψ̄_0ψ_x⟩`
(translation invariance).  The `L^{-(d-2+κ)N}` term is the constant term omitted in the paper.
The flow `V₀c` is that of `PtCorr.setup` (the flow is run with `l₀ = λ̄`; the correlation
functions do not depend on `l₀`). -/
theorem lem_2pt_one (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ (V₀c : ℝ → ℂ → Vcoup) (bbar C κ : ℝ), 0 < bbar ∧ 0 ≤ C ∧ 0 < κ ∧
      (∀ msq b₀, (V₀c msq b₀).b = b₀) ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (msq : ℝ), 0 < msq → ∀ (b₀ : ℂ), ‖b₀‖ ≤ bbar →
      ∀ x : Lam d L N, x ≠ 0 → 1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 →
      ∃ E₁ E₂ : ℂ,
        ‖E₁‖ ≤ C * ‖b₀‖ * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + κ)) ∧
        ‖E₂‖ ≤ C * ‖b₀‖ * ((supNorm x : ℝ) ^ (-κ) / (msq * Fintype.card (Lam d L N)) +
          (L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N))) ∧
        avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
            (psibar (ctr d L N) * psi (ctr d L N + x)) =
          (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) +
            (tau d L N msq + E₂) / (1 + Suscept.utN d L N msq (V₀c msq b₀)) + E₁ ∧
        avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ) (psibar 0 * psi x) =
          (WN (d := d) (n := L ^ N) stdPt msq (L : ℝ) N x : ℂ) +
            (tau d L N msq + E₂) / (1 + Suscept.utN d L N msq (V₀c msq b₀)) + E₁ := by
  obtain ⟨L₀, Kℓ, hKℓ, H⟩ := setup hd
  refine ⟨L₀, Kℓ, hKℓ, fun L _ hL hLodd => ?_⟩
  obtain ⟨A₀, hA₀, H⟩ := H L hL hLodd
  refine ⟨A₀, hA₀, fun A hA ℓ₀ hℓ₀ hKℓ' => ?_⟩
  obtain ⟨V₀c, lbar, Cf, κ, HF⟩ := H A hA ℓ₀ hℓ₀ hKℓ'
  obtain ⟨C, hC, h⟩ := lem_2pt_one_of hd HF
  exact ⟨V₀c, lbar, C, κ, HF.lbar_pos, hC, HF.κ_pos, HF.hb, h⟩

end

end PtCorr
