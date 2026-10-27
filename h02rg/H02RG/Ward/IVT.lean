import Mathlib

/-!
# An implicit-function argument by monotonicity and the intermediate value theorem

Used for `cor:ward` (ii): for functions `β, h` of `(b, m²) ∈ (0, b̄] × [0, ∞)` with
* `β, h` jointly continuous,
* `b ↦ β(b, m²)` strictly decreasing, `lo/b ≤ β(b, m²) ≤ hi/b`,
* `h(b, 0) = 0` and `h(b, m²) ≥ m² β(b, m²)/2`,

every `(β, h)` with `β ≥ β₀ := hi/b̄`, `h ≥ 0` is attained (`ivt_solution`), with a choice that is
right-continuous at `h = 0`. This replaces the reference to MR3339164, Prop. 4.2 in the paper.
-/

namespace Ward

open Filter Topology Set

/-- Continuity of the solution `B(m)` of `F(B(m), m) = y` for `F` strictly decreasing in the first
variable and continuous in the second. -/
theorem continuousOn_implicit {F : ℝ → ℝ → ℝ} {c y : ℝ} {B : ℝ → ℝ}
    (hcont : ∀ b ∈ Ioc 0 c, ContinuousOn (fun m => F b m) (Ici 0))
    (hanti : ∀ m, 0 ≤ m → StrictAntiOn (fun b => F b m) (Ioc 0 c))
    (hB : ∀ m, 0 ≤ m → B m ∈ Ioc 0 c) (hFB : ∀ m, 0 ≤ m → F (B m) m = y) :
    ContinuousOn B (Ici 0) := by
  intro m₀ hm₀
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨h0, hc⟩ := hB m₀ hm₀
  set b₀ := B m₀
  -- the lower barrier
  set bl := max (b₀ - ε / 2) (b₀ / 2) with hbl
  have hbl0 : 0 < bl := lt_max_of_lt_right (by linarith)
  have hblb : bl < b₀ := max_lt (by linarith) (by linarith)
  have hblm : bl ∈ Ioc 0 c := ⟨hbl0, by linarith⟩
  have hFl : y < F bl m₀ := by
    rw [← hFB m₀ hm₀]; exact hanti m₀ hm₀ hblm ⟨h0, hc⟩ hblb
  have ev1 : ∀ᶠ m in 𝓝[Ici 0] m₀, y < F bl m :=
    ((hcont bl hblm) m₀ hm₀).tendsto.eventually_const_lt hFl
  have ev0 : ∀ᶠ m in 𝓝[Ici 0] m₀, m ∈ Ici (0 : ℝ) := self_mem_nhdsWithin
  -- the lower bound `bl < B m`
  have low : ∀ᶠ m in 𝓝[Ici 0] m₀, bl < B m := by
    filter_upwards [ev1, ev0] with m h1 hm
    by_contra hle
    rw [not_lt] at hle
    have hBm := hB m hm
    have : F bl m ≤ F (B m) m := (hanti m hm).antitoneOn hBm hblm hle
    rw [hFB m hm] at this
    linarith
  -- the upper bound `B m < b₀ + ε`
  have up : ∀ᶠ m in 𝓝[Ici 0] m₀, B m < b₀ + ε := by
    rcases hc.lt_or_eq with hlt | heq
    · set bu := min (b₀ + ε / 2) c with hbu
      have hbub : b₀ < bu := lt_min (by linarith) hlt
      have hbum : bu ∈ Ioc 0 c := ⟨by linarith, min_le_right _ _⟩
      have hFu : F bu m₀ < y := by
        rw [← hFB m₀ hm₀]; exact hanti m₀ hm₀ ⟨h0, hc⟩ hbum hbub
      have ev2 : ∀ᶠ m in 𝓝[Ici 0] m₀, F bu m < y :=
        ((hcont bu hbum) m₀ hm₀).tendsto.eventually_lt_const hFu
      filter_upwards [ev2, ev0] with m h2 hm
      by_contra hle
      rw [not_lt] at hle
      have hBm := hB m hm
      have hle' : bu ≤ B m := le_trans (min_le_left _ _) (by linarith)
      have : F (B m) m ≤ F bu m := (hanti m hm).antitoneOn hbum hBm hle'
      rw [hFB m hm] at this
      linarith
    · filter_upwards [ev0] with m hm
      have := (hB m hm).2
      linarith
  filter_upwards [low, up] with m h1 h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [le_max_left (b₀ - ε / 2) (b₀ / 2)]

/-- **The IVT solution** (abstract form of `cor:ward` (ii)). -/
theorem ivt_solution {β h : ℝ → ℝ → ℝ} {c lo hi : ℝ} (hc : 0 < c) (hlo : 0 < lo)
    (hlohi : lo ≤ hi)
    (hβc : ContinuousOn (fun p : ℝ × ℝ => β p.1 p.2) (Ioc 0 c ×ˢ Ici 0))
    (hhc : ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2) (Ioc 0 c ×ˢ Ici 0))
    (hanti : ∀ m, 0 ≤ m → StrictAntiOn (fun b => β b m) (Ioc 0 c))
    (hbd : ∀ b m, 0 < b → b ≤ c → 0 ≤ m → lo / b ≤ β b m ∧ β b m ≤ hi / b)
    (hh0 : ∀ b, 0 < b → b ≤ c → h b 0 = 0)
    (hhm : ∀ b m, 0 < b → b ≤ c → 0 ≤ m → m * β b m / 2 ≤ h b m) :
    ∃ (β₀ : ℝ) (bt mt : ℝ → ℝ → ℝ), 0 < β₀ ∧ ∀ β', β₀ ≤ β' → ∀ h', 0 ≤ h' →
      0 < bt β' h' ∧ bt β' h' ≤ c ∧ 0 ≤ mt β' h' ∧ (0 < h' → 0 < mt β' h') ∧
      β (bt β' h') (mt β' h') = β' ∧ h (bt β' h') (mt β' h') = h' ∧
      mt β' 0 = 0 ∧ Tendsto (mt β') (𝓝[≥] 0) (𝓝 0) ∧
      Tendsto (bt β') (𝓝[≥] 0) (𝓝 (bt β' 0)) ∧
      (∀ b, 0 < b → b ≤ c → β b 0 = β' → b = bt β' 0) := by
  set β₀ := hi / c with hβ₀
  have hβ₀pos : 0 < β₀ := div_pos (hlo.trans_le hlohi) hc
  have hcont1 : ∀ m, 0 ≤ m → ContinuousOn (fun b => β b m) (Ioc 0 c) := fun m hm =>
    hβc.comp (continuousOn_id.prodMk continuousOn_const) fun b hb => ⟨hb, hm⟩
  have hcont2 : ∀ b ∈ Ioc 0 c, ContinuousOn (fun m => β b m) (Ici 0) := fun b hb =>
    hβc.comp (continuousOn_const.prodMk continuousOn_id) fun m hm => ⟨hb, hm⟩
  -- existence of `B(β', m)`
  have hex : ∀ β', β₀ ≤ β' → ∀ m, 0 ≤ m → ∃ b, b ∈ Ioc 0 c ∧ β b m = β' := by
    intro β' hβ' m hm
    have hβ'0 : 0 < β' := hβ₀pos.trans_le hβ'
    set a := lo / β' with ha
    have ha0 : 0 < a := div_pos hlo hβ'0
    have hac : a ≤ c := by
      rw [ha, div_le_iff₀ hβ'0]
      have := mul_le_mul_of_nonneg_left hβ' hc.le
      rw [hβ₀, mul_div_cancel₀ _ hc.ne'] at this
      linarith
    have hsub : Icc a c ⊆ Ioc 0 c := fun x hx => ⟨ha0.trans_le hx.1, hx.2⟩
    have hfa : β' ≤ β a m := by
      have := (hbd a m ha0 hac hm).1
      rwa [ha, div_div_cancel₀ hlo.ne'] at this
    have hfc : β c m ≤ β' := by
      exact (hbd c m hc le_rfl hm).2.trans hβ'
    obtain ⟨b, hb, hbe⟩ := intermediate_value_Icc' hac ((hcont1 m hm).mono hsub) ⟨hfc, hfa⟩
    exact ⟨b, hsub hb, hbe⟩
  choose! B hB hBe using hex
  -- continuity of `B(β', ·)`
  have hBc : ∀ β', β₀ ≤ β' → ContinuousOn (B β') (Ici 0) := fun β' hβ' =>
    continuousOn_implicit hcont2 hanti (fun m hm => hB β' hβ' m hm) (fun m hm => hBe β' hβ' m hm)
  -- the function `H(m) = h(B(m), m)`
  have hHc : ∀ β', β₀ ≤ β' → ContinuousOn (fun m => h (B β' m) m) (Ici 0) := fun β' hβ' =>
    hhc.comp ((hBc β' hβ').prodMk continuousOn_id) fun m hm => ⟨hB β' hβ' m hm, hm⟩
  -- existence of `m̃²`
  have hexm : ∀ β', β₀ ≤ β' → ∀ h', 0 ≤ h' →
      ∃ m, m ∈ Icc 0 (2 * h' / β') ∧ h (B β' m) m = h' := by
    intro β' hβ' h' hh'
    have hβ'0 : 0 < β' := hβ₀pos.trans_le hβ'
    have hle : 0 ≤ 2 * h' / β' := by positivity
    have hH0 : h (B β' 0) 0 = 0 := hh0 _ (hB β' hβ' 0 le_rfl).1 (hB β' hβ' 0 le_rfl).2
    have hH1 : h' ≤ h (B β' (2 * h' / β')) (2 * h' / β') := by
      have := hhm _ _ (hB β' hβ' _ hle).1 (hB β' hβ' _ hle).2 hle
      rw [hBe β' hβ' _ hle] at this
      have e : 2 * h' / β' * β' / 2 = h' := by field_simp
      linarith
    obtain ⟨m, hm, hme⟩ := intermediate_value_Icc hle ((hHc β' hβ').mono Icc_subset_Ici_self)
      ⟨hH0.symm ▸ hh', hH1⟩
    exact ⟨m, hm, hme⟩
  choose! mt hmt hmte using hexm
  refine ⟨β₀, fun β' h' => B β' (mt β' h'), mt, hβ₀pos, fun β' hβ' h' hh' => ?_⟩
  have hβ'0 : 0 < β' := hβ₀pos.trans_le hβ'
  have hmt0 : ∀ h', 0 ≤ h' → 0 ≤ mt β' h' := fun h' hh' => (hmt β' hβ' h' hh').1
  have hmt00 : mt β' 0 = 0 := by
    have := hmt β' hβ' 0 le_rfl
    simp only [mul_zero, zero_div, mem_Icc] at this
    linarith [this.1, this.2]
  have hmtT : Tendsto (mt β') (𝓝[≥] 0) (𝓝 0) := by
    have hup : Tendsto (fun h' : ℝ => 2 * h' / β') (𝓝[≥] 0) (𝓝 0) := by
      have : Tendsto (fun h' : ℝ => 2 * h' / β') (𝓝 0) (𝓝 (2 * 0 / β')) :=
        ((continuous_const.mul continuous_id).div_const β').tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx using hmt0 x hx
    · filter_upwards [self_mem_nhdsWithin] with x hx using (hmt β' hβ' x hx).2
  refine ⟨(hB β' hβ' _ (hmt0 h' hh')).1, (hB β' hβ' _ (hmt0 h' hh')).2, hmt0 h' hh', ?_,
    hBe β' hβ' _ (hmt0 h' hh'), hmte β' hβ' h' hh', hmt00, hmtT, ?_, ?_⟩
  · intro hpos
    rcases (hmt0 h' hh').lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have := hmte β' hβ' h' hh'
      rw [← heq, hh0 _ (hB β' hβ' 0 le_rfl).1 (hB β' hβ' 0 le_rfl).2] at this
      linarith
  · show Tendsto (fun h' => B β' (mt β' h')) (𝓝[≥] 0) (𝓝 (B β' (mt β' 0)))
    rw [hmt00]
    have hB0 := (hBc β' hβ' 0 self_mem_Ici).tendsto
    refine hB0.comp (tendsto_nhdsWithin_iff.2 ⟨hmtT, ?_⟩)
    filter_upwards [self_mem_nhdsWithin] with x hx using hmt0 x hx
  · intro b hb hbc hbe
    show b = B β' (mt β' 0)
    rw [hmt00]
    exact (hanti 0 le_rfl).injOn ⟨hb, hbc⟩ (hB β' hβ' 0 le_rfl)
      (show β b 0 = β (B β' 0) 0 by rw [hbe, hBe β' hβ' 0 le_rfl])

end Ward
