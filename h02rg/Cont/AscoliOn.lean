import Cont.AscoliStep

/-!
# Asymptotic Arzelà–Ascoli on `{r ≤ dist x x₀}` and on `{r₀ < dist x x₀}`

Variants of `Cont/AscoliStep.lean` for the `r`-dependent equicontinuity of B3:

* `ascoli_asymp_exists_subseq_on` : one compact set `K` (hypotheses on `K` only); the limit is
  uniformly continuous on `K` and the convergence is uniform on `K`;
* `ascoli_asymp_exists_subseq_annulus` : for a compact metric space, hypotheses on every
  `{r ≤ dist x x₀}` with `r > r₀`; the limit is continuous on `{r₀ < dist x x₀}`, and the
  convergence is uniform on every compact subset of it (`r₀ = 0` is the punctured case).
-/

set_option autoImplicit false

namespace Cont

open Filter Topology Set Metric

section AscoliOn

variable {X : Type*} [PseudoMetricSpace X]

/-- **Asymptotic Arzelà–Ascoli on one compact set.** -/
theorem ascoli_asymp_exists_subseq_on (K : Set X) (hK : IsCompact K) (f : ℕ → X → ℝ)
    (hb : ∃ C, ∀ N, ∀ x ∈ K, |f N x| ≤ C)
    (heq : ∀ η > 0, ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈ K, ∀ y ∈ K,
      dist x y < δ → |f N x - f N y| ≤ η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : X → ℝ,
      UniformContinuousOn g K ∧ TendstoUniformlyOn (fun m => f (φ m)) g atTop K := by
  obtain ⟨φ, hφ, g, hg⟩ := ascoli_asymp_exists_subseq_exhaust (fun _ => K) (fun _ => hK) f
    (fun _ => hb) (fun _ => heq)
  exact ⟨φ, hφ, g, hg 0⟩

end AscoliOn

section AscoliAnnulus

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Asymptotic Arzelà–Ascoli on `{r₀ < dist x x₀}`**: hypotheses on each `{r ≤ dist x x₀}`,
`r > r₀`. -/
theorem ascoli_asymp_exists_subseq_annulus (x₀ : X) (r₀ : ℝ) (f : ℕ → X → ℝ)
    (hb : ∀ r > r₀, ∃ C, ∀ N x, r ≤ dist x x₀ → |f N x| ≤ C)
    (heq : ∀ r > r₀, ∀ η > 0, ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y,
      r ≤ dist x x₀ → r ≤ dist y x₀ → dist x y < δ → |f N x - f N y| ≤ η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : X → ℝ, ContinuousOn g {x | r₀ < dist x x₀} ∧
      (∀ r > r₀, UniformContinuousOn g {x | r ≤ dist x x₀}) ∧
      ∀ K ⊆ {x | r₀ < dist x x₀}, IsCompact K →
        TendstoUniformlyOn (fun m => f (φ m)) g atTop K := by
  let K : ℕ → Set X := fun n => {x | r₀ + 1 / ((n : ℝ) + 1) ≤ dist x x₀}
  have hpos : ∀ n : ℕ, r₀ < r₀ + 1 / ((n : ℝ) + 1) := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hK : ∀ n, IsCompact (K n) := fun n =>
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  obtain ⟨φ, hφ, g, hg⟩ := ascoli_asymp_exists_subseq_exhaust K hK f
    (fun n => by
      obtain ⟨C, hC⟩ := hb _ (hpos n)
      exact ⟨C, fun N x hx => hC N x hx⟩)
    (fun n η hη => by
      obtain ⟨δ, hδ, N₀, hN₀⟩ := heq _ (hpos n) η hη
      exact ⟨δ, hδ, N₀, fun N hN x hx y hy hxy => hN₀ N hN x y hx hy hxy⟩)
  have hsub : ∀ r > r₀, ∃ n, {x | r ≤ dist x x₀} ⊆ K n := fun r hr => by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hr)
    exact ⟨n, fun x (hx : r ≤ dist x x₀) => (show r₀ + 1 / ((n : ℝ) + 1) ≤ dist x x₀ by linarith)⟩
  have huc : ∀ r > r₀, UniformContinuousOn g {x | r ≤ dist x x₀} := fun r hr => by
    obtain ⟨n, hn⟩ := hsub r hr
    exact (hg n).1.mono hn
  refine ⟨φ, hφ, g, ?_, huc, ?_⟩
  · intro x (hx : r₀ < dist x x₀)
    have hmid : r₀ < (r₀ + dist x x₀) / 2 := by linarith
    have hmem : {y | (r₀ + dist x x₀) / 2 ≤ dist y x₀} ∈ 𝓝 x := by
      refine mem_of_superset ((isOpen_lt continuous_const
        (continuous_id.dist continuous_const)).mem_nhds (show (r₀ + dist x x₀) / 2 < dist x x₀ by
          linarith)) fun y (hy : (r₀ + dist x x₀) / 2 < dist y x₀) =>
        (show (r₀ + dist x x₀) / 2 ≤ dist y x₀ from hy.le)
    exact ((huc _ hmid).continuousOn.continuousAt hmem).continuousWithinAt
  · intro L hL hLc
    rcases L.eq_empty_or_nonempty with rfl | hne
    · exact tendstoUniformlyOn_empty
    obtain ⟨x₁, hx₁, hmin⟩ := hLc.exists_isMinOn hne (continuous_id.dist continuous_const).continuousOn
    obtain ⟨n, hn⟩ := hsub (dist x₁ x₀) (hL hx₁)
    exact (hg n).2.mono fun y hy => hn (hmin hy)

end AscoliAnnulus

end Cont
