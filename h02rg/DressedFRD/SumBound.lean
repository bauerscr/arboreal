import DressedFRD.WordBound

/-!
# Summing words (`lem:sum`)

With `S = 𝒮_j = ∑_r W_{r-j} |Z_j| ‖R_{j,r}‖_{(r-1)}` and
`σ₀ = θ^{-3/256} + θ^{-2/256} C_ρ S`:
* `words_k_bound`: `∑_{|w|=k+2} W_{s(w)-1-j} |ζ'|^{k+1} ‖O_w‖_{(s(w)-1)} ≤ b_k`, where
  `b_k = |ζ'| L^c η^k (c₂ (θ^{-3/256})^{k+2} + (k+2) θ^{-2/256} S σ₀^{k+1})`;
* `scales_bound`: `∑_{s=j+2}^N W_{s-1-j} ‖w_s‖_{(s-1)} ≤ |ζ'| L^c (2 c₂ θ^{-6/256} + 6 θ^{-2/256} S σ₀)`,
  if `η θ^{-3/256} ≤ 1/2` and `η σ₀ ≤ 1/2`.
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

namespace Data

variable {D : Data d n} {q : ℕ} {c₂ θ : ℝ} {j : ℕ}

/-- `𝒮_j`. -/
def Sj (D : Data d n) (q : ℕ) (θ : ℝ) (j : ℕ) : ℝ :=
  ∑ r ∈ Ioc j D.N, Wt θ D.L (r - j) * D.tW q j r

/-- `σ₀ = θ^{-3/256} + θ^{-2/256} C_ρ 𝒮_j`. -/
def sig0 (D : Data d n) (q : ℕ) (θ : ℝ) (j : ℕ) : ℝ :=
  θ ^ (-(3 : ℝ) / 256) + θ ^ (-(2 : ℝ) / 256) * Crho d D.L * D.Sj q θ j

theorem Sj_nonneg (hθ : 0 < θ) (hL : 1 ≤ D.L) : 0 ≤ D.Sj q θ j :=
  sum_nonneg fun r _ => mul_nonneg (Wt_pos hθ _ _).le (tW_nonneg hL q j r)

theorem sum_tailW (hL : 1 ≤ D.L) :
    ∑ ℓ ∈ alph j D.N, D.tailW q θ j ℓ = θ ^ (-(2 : ℝ) / 256) * D.Sj q θ j := by
  simp [alph, tailW, Sj, Finset.mul_sum, mul_assoc]

theorem sum_omg_beta_le (H : D.StepHyp q c₂ θ j) (κ : Fin 3) :
    ∑ ℓ ∈ alph j D.N, D.omg θ j κ ℓ * beta (fun r => Crho d D.L * D.tW q j r) ℓ ≤
      D.sig0 q θ j := by
  have hL1 : 1 ≤ D.L := by have := H.hL; omega
  have hL0 : (0 : ℝ) ≤ D.L := by positivity
  simp only [alph, sum_insert (show (none : Option ℕ) ∉ (Ioc j D.N).map ⟨some, Option.some_injective _⟩
    by simp), sum_map, Function.Embedding.coeFn_mk, beta, mul_one, sig0, Sj]
  refine add_le_add (omg_none_le H.hθ H.hθ1 hL1 j κ) ?_
  rw [Finset.mul_sum]
  refine sum_le_sum fun r hr => ?_
  rw [mem_Ioc] at hr
  have h1 := omg_some_le (D := D) H.hθ H.hθ1 hL1 hr.1.le κ
  have h2 : 0 ≤ Crho d D.L * D.tW q j r := mul_nonneg (Crho_nonneg d hL0) (tW_nonneg hL1 q j r)
  calc D.omg θ j κ (some r) * (Crho d D.L * D.tW q j r)
      ≤ θ ^ (-(2 : ℝ) / 256) * Wt θ D.L (r - j) * (Crho d D.L * D.tW q j r) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := by ring

/-- The bound for all words of length `k + 2`. -/
theorem words_k_bound (H : D.StepHyp q c₂ θ j) {η : ℝ} (hη : 0 ≤ η)
    (hη2 : η ^ 2 = ‖D.zp j‖) (hηc : η ≤ (D.L : ℝ) ^ (-cexp d q)) (k : ℕ) :
    ∑ w ∈ words j D.N k, Wt θ D.L (scale D.L j D.N (rbar (D.rbV j) w) - 1 - j) *
        ‖D.zp j‖ ^ (k + 1) *
        snorm D.L q (scale D.L j D.N (rbar (D.rbV j) w) - 1) (wordVal (D.letV j (D.tails j)) w) ≤
      ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q * η ^ k *
        (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2) +
          (k + 2) * (θ ^ (-(2 : ℝ) / 256) * D.Sj q θ j) * D.sig0 q θ j ^ (k + 1)) := by
  have hL7 := H.hL
  have hL1 : 1 ≤ D.L := by omega
  have hL0 : (0 : ℝ) ≤ D.L := by positivity
  set ρ : ℕ → ℝ := fun r => Crho d D.L * D.tW q j r
  have hρ0 : ∀ r, 0 ≤ ρ r := fun r => mul_nonneg (Crho_nonneg d hL0) (tW_nonneg hL1 q j r)
  set std : Fin (k + 2) → Option ℕ := fun _ => none
  have hstd : std ∈ words j D.N k := Fintype.mem_piFinset.2 fun _ => none_mem_alph j D.N
  set G : Fin (k + 2) → (Fin (k + 2) → Option ℕ) → ℝ := fun p w =>
    D.tailW q θ j (w p) * ∏ i ∈ univ.erase p, D.omg θ j (kindOf i) (w i) * beta ρ (w i)
  have hG0 : ∀ p w, 0 ≤ G p w := by
    intro p w
    refine mul_nonneg ?_ (prod_nonneg fun i _ =>
      mul_nonneg (omg_pos H.hθ j _ _).le (beta_nonneg hρ0 _))
    rcases w p with _ | r
    · simp [tailW]
    · simp only [tailW]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg H.hθ.le _) (Wt_pos H.hθ _ _).le)
        (tW_nonneg hL1 q j r)
  set K := ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q * η ^ k
  have hK0 : 0 ≤ K := by positivity
  set f : (Fin (k + 2) → Option ℕ) → ℝ := fun w =>
    Wt θ D.L (scale D.L j D.N (rbar (D.rbV j) w) - 1 - j) * ‖D.zp j‖ ^ (k + 1) *
      snorm D.L q (scale D.L j D.N (rbar (D.rbV j) w) - 1) (wordVal (D.letV j (D.tails j)) w)
  -- per-word bound
  have hper : ∀ w ∈ words j D.N k, f w ≤
      (if w = std then K * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2)) else 0) +
        K * ∑ p, G p w := by
    intro w hw
    by_cases htail : ∃ i r, w i = some r
    · obtain ⟨p, r, hp, hmax⟩ := exists_max_tail htail
      have hne : w ≠ std := fun h => by rw [h] at hp; simp [std] at hp
      rw [if_neg hne, zero_add]
      refine (word_tail_bound H hη hη2 hηc hw hp hmax).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hK0
      exact single_le_sum (f := fun p => G p w) (fun p _ => hG0 p w) (mem_univ p)
    · have hw' : w = std := by
        funext i
        rcases h : w i with _ | r
        · rfl
        · exact absurd ⟨i, r, h⟩ htail
      subst hw'
      rw [if_pos rfl]
      have := word_std_bound H hη hη2 hηc k
      have h2 : 0 ≤ K * ∑ p, G p std := mul_nonneg hK0 (sum_nonneg fun p _ => hG0 p _)
      exact le_add_of_le_of_nonneg this h2
  -- product structure of the `G`-sums
  have hprod : ∀ p, ∑ w ∈ words j D.N k, G p w ≤
      (θ ^ (-(2 : ℝ) / 256) * D.Sj q θ j) * D.sig0 q θ j ^ (k + 1) := by
    intro p
    set g : Fin (k + 2) → Option ℕ → ℝ := fun i ℓ =>
      if i = p then D.tailW q θ j ℓ else D.omg θ j (kindOf i) ℓ * beta ρ ℓ
    have hGg : ∀ w, G p w = ∏ i, g i (w i) := by
      intro w
      simp only [G, g]
      rw [← mul_prod_erase _ _ (mem_univ p), if_pos rfl]
      congr 1
      exact prod_congr rfl fun i hi => by rw [if_neg (ne_of_mem_erase hi)]
    simp only [hGg]
    unfold words
    rw [← Finset.prod_univ_sum (fun _ => alph j D.N) g]
    rw [← mul_prod_erase _ _ (mem_univ p)]
    simp only [g, if_pos rfl]
    rw [sum_tailW hL1]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.rpow_nonneg H.hθ.le _)
      (Sj_nonneg H.hθ hL1))
    calc ∏ i ∈ univ.erase p, ∑ ℓ ∈ alph j D.N,
          (if i = p then D.tailW q θ j ℓ else D.omg θ j (kindOf i) ℓ * beta ρ ℓ)
        ≤ ∏ _i ∈ univ.erase p, D.sig0 q θ j := by
          refine prod_le_prod (fun i hi => sum_nonneg fun ℓ _ => ?_) fun i hi => ?_
          · rw [if_neg (ne_of_mem_erase hi)]
            exact mul_nonneg (omg_pos H.hθ j _ _).le (beta_nonneg hρ0 _)
          · simp only [if_neg (ne_of_mem_erase hi)]
            exact sum_omg_beta_le H (kindOf i)
      _ = D.sig0 q θ j ^ (k + 1) := by
          rw [prod_const, card_erase_of_mem (mem_univ p), card_univ, Fintype.card_fin]; rfl
  calc ∑ w ∈ words j D.N k, f w
      ≤ ∑ w ∈ words j D.N k, ((if w = std then K * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2))
          else 0) + K * ∑ p, G p w) := sum_le_sum hper
    _ = K * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2)) + K * ∑ p, ∑ w ∈ words j D.N k, G p w := by
        rw [sum_add_distrib, sum_ite_eq' (words j D.N k) std, if_pos hstd, ← mul_sum, sum_comm]
    _ ≤ K * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ (k + 2)) +
          K * ∑ _p : Fin (k + 2), (θ ^ (-(2 : ℝ) / 256) * D.Sj q θ j) * D.sig0 q θ j ^ (k + 1) := by
        gcongr with p; exact hprod p
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring

theorem summable_geom_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : Summable fun k : ℕ => x ^ k :=
  summable_geometric_of_lt_one h0 (by linarith)

theorem tsum_geom_half_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : ∑' k : ℕ, x ^ k ≤ 2 := by
  rw [tsum_geometric_of_lt_one h0 (by linarith)]
  rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith

theorem summable_k2_half {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) :
    Summable fun k : ℕ => ((k : ℝ) + 2) * y ^ k := by
  have hy : ‖y‖ < 1 := by rw [Real.norm_of_nonneg h0]; linarith
  have h1' := (summable_pow_mul_geometric_of_norm_lt_one 1 hy)
  simp only [pow_one] at h1'
  have h2 := (summable_geometric_of_lt_one h0 (by linarith : y < 1)).mul_left 2
  simpa [add_mul] using h1'.add h2

theorem tsum_k2_half_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) :
    ∑' k : ℕ, ((k : ℝ) + 2) * y ^ k ≤ 6 := by
  have hy : ‖y‖ < 1 := by rw [Real.norm_of_nonneg h0]; linarith
  have h1' := (summable_pow_mul_geometric_of_norm_lt_one 1 hy)
  simp only [pow_one] at h1'
  have h2 := (summable_geometric_of_lt_one h0 (by linarith : y < 1))
  have e : (fun k : ℕ => ((k : ℝ) + 2) * y ^ k) = fun k : ℕ => (k : ℝ) * y ^ k + 2 * y ^ k := by
    funext k; ring
  rw [e, h1'.tsum_add (h2.mul_left 2), tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hy,
    tsum_geometric_of_lt_one h0 (by linarith)]
  have h3 : y / (1 - y) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith
  have h4 : 2 * (1 - y)⁻¹ ≤ 4 := by
    have : (1 - y)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  linarith

/-- The words assigned to the scales `s ≥ j + 1` (`lem:sum`(b), without the tails of `R_j`). -/
theorem scales_bound_all (H : D.StepHyp q c₂ θ j) {η : ℝ} (hη : 0 ≤ η)
    (hη2 : η ^ 2 = ‖D.zp j‖) (hηc : η ≤ (D.L : ℝ) ^ (-cexp d q))
    (hx : η * θ ^ (-(3 : ℝ) / 256) ≤ 1 / 2) (hy : η * D.sig0 q θ j ≤ 1 / 2)
    (hden : ∀ m, ‖D.zp j * D.eps j (D.tails j) m‖ < 1) :
    ∑ s ∈ Icc (j + 1) D.N, Wt θ D.L (s - 1 - j) * snorm D.L q (s - 1) (D.wSc j (D.tails j) s) ≤
      ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q *
        (2 * (c₂ * (θ ^ (-(3 : ℝ) / 256)) ^ 2) +
          6 * (θ ^ (-(2 : ℝ) / 256) * D.Sj q θ j * D.sig0 q θ j)) := by
  have hL7 := H.hL
  have hL1 : 1 ≤ D.L := by omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hj1 : j + 1 ≤ D.N := H.hj
  have hS0 := Sj_nonneg (D := D) (q := q) (j := j) H.hθ hL1
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg hL0 _) (H.loc 0 (by have := H.hj; omega))
  set a := θ ^ (-(3 : ℝ) / 256)
  have ha0 : 0 ≤ a := Real.rpow_nonneg H.hθ.le _
  set σ := D.sig0 q θ j
  have hσ0 : 0 ≤ σ := add_nonneg ha0 (mul_nonneg (mul_nonneg (Real.rpow_nonneg H.hθ.le _)
    (Crho_nonneg d hL0.le)) hS0)
  set b2 := θ ^ (-(2 : ℝ) / 256)
  have hb20 : 0 ≤ b2 := Real.rpow_nonneg H.hθ.le _
  set K0 := ‖D.zp j‖ * (D.L : ℝ) ^ cexp d q
  have hK0 : 0 ≤ K0 := by positivity
  -- the majorant `b k`
  set A1 := K0 * (c₂ * a ^ 2)
  set A2 := K0 * (b2 * D.Sj q θ j * σ)
  have hA1 : 0 ≤ A1 := by positivity
  have hA2 : 0 ≤ A2 := by positivity
  set b : ℕ → ℝ := fun k => A1 * (η * a) ^ k + A2 * (((k : ℝ) + 2) * (η * σ) ^ k)
  have hb_eq : ∀ k, K0 * η ^ k * (c₂ * a ^ (k + 2) + (k + 2) * (b2 * D.Sj q θ j) * σ ^ (k + 1)) =
      b k := by
    intro k; simp only [b, A1, A2]; ring
  have hbs : Summable b :=
    ((summable_geom_half (by positivity) hx).mul_left A1).add
      ((summable_k2_half (by positivity) hy).mul_left A2)
  have hbsum : ∑' k, b k ≤ 2 * A1 + 6 * A2 := by
    rw [((summable_geom_half (by positivity) hx).mul_left A1).tsum_add
      ((summable_k2_half (by positivity) hy).mul_left A2), tsum_mul_left, tsum_mul_left]
    have := tsum_geom_half_le (by positivity) hx
    have := tsum_k2_half_le (by positivity) hy
    nlinarith
  -- the per-scale word sums
  set F : ℕ → ℕ → ℝ := fun s k =>
    ∑ w ∈ (words j D.N k).filter (fun w => scale D.L j D.N (rbar (D.rbV j) w) = s),
      Wt θ D.L (scale D.L j D.N (rbar (D.rbV j) w) - 1 - j) * ‖D.zp j‖ ^ (k + 1) *
        snorm D.L q (scale D.L j D.N (rbar (D.rbV j) w) - 1) (wordVal (D.letV j (D.tails j)) w)
  have hF0 : ∀ s k, 0 ≤ F s k := fun s k => sum_nonneg fun w _ => by
    have := (Wt_pos H.hθ D.L (scale D.L j D.N (rbar (D.rbV j) w) - 1 - j)).le
    have := snorm_nonneg hL0 (q := q) (s := scale D.L j D.N (rbar (D.rbV j) w) - 1)
      (wordVal (D.letV j (D.tails j)) w)
    positivity
  have hFsum : ∀ k, ∑ s ∈ Icc (j + 1) D.N, F s k ≤ b k := by
    intro k
    rw [← hb_eq k]
    have := words_k_bound H hη hη2 hηc k
    refine le_trans (le_of_eq ?_) this
    exact sum_fiberwise_of_maps_to (fun w _ => by rw [mem_Icc]; exact ⟨le_scale, scale_le hj1⟩) _
  have hFle : ∀ s ∈ Icc (j + 1) D.N, ∀ k, F s k ≤ b k := fun s hs k =>
    (single_le_sum (f := fun s => F s k) (fun s _ => hF0 s k) hs).trans (hFsum k)
  -- each scale
  have hterm : ∀ s ∈ Icc (j + 1) D.N, ∀ k, Wt θ D.L (s - 1 - j) *
      snorm D.L q (s - 1) (D.zp j ^ (k + 1) • D.wLen j (D.tails j) s k) ≤ F s k := by
    intro s hs k
    rw [snorm_smul hL0, norm_pow]
    have hsum := snorm_sum_le (q := q) (s := s - 1) hL0
      ((words j D.N k).filter (fun w => scale D.L j D.N (rbar (D.rbV j) w) = s))
      (fun w => wordVal (D.letV j (D.tails j)) w)
    calc Wt θ D.L (s - 1 - j) * (‖D.zp j‖ ^ (k + 1) * snorm D.L q (s - 1) (D.wLen j (D.tails j) s k))
        ≤ Wt θ D.L (s - 1 - j) * (‖D.zp j‖ ^ (k + 1) *
            ∑ w ∈ (words j D.N k).filter (fun w => scale D.L j D.N (rbar (D.rbV j) w) = s),
              snorm D.L q (s - 1) (wordVal (D.letV j (D.tails j)) w)) := by
          gcongr
          · exact (Wt_pos H.hθ _ _).le
          · exact hsum
      _ = F s k := by
          simp only [F, mul_sum]
          refine sum_congr rfl fun w hw => ?_
          rw [(mem_filter.1 hw).2]; ring
  have hsumm : ∀ s ∈ Icc (j + 1) D.N, Summable fun k =>
      snorm D.L q (s - 1) (D.zp j ^ (k + 1) • D.wLen j (D.tails j) s k) := by
    intro s hs
    refine Summable.of_nonneg_of_le (fun k => snorm_nonneg hL0 _) (fun k => ?_) hbs
    have h1 := hterm s hs k
    have h2 := one_le_Wt H.hθ H.hθ1 hL0.le (s - 1 - j)
    have h3 := snorm_nonneg hL0 (q := q) (s := s - 1) (D.zp j ^ (k + 1) • D.wLen j (D.tails j) s k)
    nlinarith [hFle s hs k]
  have hscale : ∀ s ∈ Icc (j + 1) D.N, snorm D.L q (s - 1) (D.wSc j (D.tails j) s) ≤
      ∑' k, snorm D.L q (s - 1) (D.zp j ^ (k + 1) • D.wLen j (D.tails j) s k) := by
    intro s hs
    exact snorm_le_tsum hL0 (fun m => hasSum_wSc H.std hL1 j hj1 (D.tails j) m (hden m) hs)
      (hsumm s hs)
  have hsub : Icc (j + 1) D.N ⊆ Icc (j + 1) D.N := subset_rfl
  calc ∑ s ∈ Icc (j + 1) D.N, Wt θ D.L (s - 1 - j) * snorm D.L q (s - 1) (D.wSc j (D.tails j) s)
      ≤ ∑ s ∈ Icc (j + 1) D.N, ∑' k, Wt θ D.L (s - 1 - j) *
          snorm D.L q (s - 1) (D.zp j ^ (k + 1) • D.wLen j (D.tails j) s k) := by
        refine sum_le_sum fun s hs => ?_
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (hscale s (hsub hs)) (Wt_pos H.hθ _ _).le
    _ = ∑' k, ∑ s ∈ Icc (j + 1) D.N, Wt θ D.L (s - 1 - j) *
          snorm D.L q (s - 1) (D.zp j ^ (k + 1) • D.wLen j (D.tails j) s k) :=
        (Summable.tsum_finsetSum fun s hs => (hsumm s (hsub hs)).mul_left _).symm
    _ ≤ ∑' k, b k := by
        refine Summable.tsum_le_tsum (fun k => ?_) (summable_sum fun s hs =>
          (hsumm s (hsub hs)).mul_left _) hbs
        calc ∑ s ∈ Icc (j + 1) D.N, Wt θ D.L (s - 1 - j) *
              snorm D.L q (s - 1) (D.zp j ^ (k + 1) • D.wLen j (D.tails j) s k)
            ≤ ∑ s ∈ Icc (j + 1) D.N, F s k := sum_le_sum fun s hs => hterm s (hsub hs) k
          _ ≤ b k := hFsum k
    _ ≤ 2 * A1 + 6 * A2 := hbsum
    _ = _ := by simp only [A1, A2, K0]; ring

end Data

end

end DressedFRD
