import Flow.StableManifold

/-!
# Continuity of the stable manifold with respect to a weak topology

`Flow.continuous_stableMap` requires the maps `B_j`, `D_j`, `g_j` of the dynamical system to
depend continuously on the parameter in the *norm* topology of the spaces `W j`.  For the
renormalisation group flow of Section `sec:flow` the spaces `W j` contain families of torus
activities (`Flow.KFam`), and the continuity in `m²` is only known torus by torus (i.e. for the
projections to the individual tori, `Step.Knext_continuousOn_msq`).

Here we prove the variant needed for this situation: continuity is measured through a family of
continuous linear "observables" `π j i : W j →L[ℂ] Y j i`.  If `B_j` maps observably continuous
bounded families to continuous families, and `D_j` and `g_j` preserve observable continuity, then
the stable manifold map is continuous in the parameter (`continuous_stableMap_obs`).  The proof
follows `continuous_stableMap`: the Picard iterates are observably continuous, and converge
uniformly (hence also after applying the `π j i`).
-/

open Filter Topology Metric Set Finset

noncomputable section

namespace Flow

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {W : ℕ → Type*} [∀ j, NormedAddCommGroup (W j)] [∀ j, NormedSpace ℂ (W j)]
  [∀ j, CompleteSpace (W j)]
variable {ι : ℕ → Type*} {Y : ∀ j, ι j → Type*} [∀ j i, NormedAddCommGroup (Y j i)]
  [∀ j i, NormedSpace ℂ (Y j i)]
variable {P : Type*} [TopologicalSpace P]

/-- A family `m ↦ w m ∈ W j` is *observably continuous* if all observables `π j i (w m)` are
continuous in `m`. -/
def ObsCont (π : ∀ j (i : ι j), W j →L[ℂ] Y j i) (j : ℕ) (w : P → W j) : Prop :=
  ∀ i, Continuous fun m => π j i (w m)

theorem ObsCont.add {π : ∀ j (i : ι j), W j →L[ℂ] Y j i} {j : ℕ} {w w' : P → W j}
    (h : ObsCont π j w) (h' : ObsCont π j w') : ObsCont π j (fun m => w m + w' m) := fun i => by
  simp only [_root_.map_add]; exact (h i).add (h' i)

theorem ObsCont.const (π : ∀ j (i : ι j), W j →L[ℂ] Y j i) {j : ℕ} (w : W j) :
    ObsCont (P := P) π j (fun _ => w) := fun _ => continuous_const

variable {β δ γ r θ R : ℝ}

/-- **Continuity of the stable manifold in a parameter, through observables.** -/
theorem continuous_stableMap_obs (π : ∀ j (i : ι j), W j →L[ℂ] Y j i)
    (S : P → System V W) (hS : ∀ m, (S m).Bounds β δ γ r)
    (hc : Admissible β δ γ r θ R)
    (hE : ∀ x, Continuous fun m => (S m).E x)
    (hB : ∀ j (w : P → W j), ObsCont π j w → (∃ M, ∀ m, ‖w m‖ ≤ M) →
      Continuous fun m => (S m).B j (w m))
    (hD : ∀ j (w : P → W j), ObsCont π j w → (∃ M, ∀ m, ‖w m‖ ≤ M) →
      ObsCont π (j + 1) fun m => (S m).D j (w m))
    (hg : ∀ j (v : P → V) (w : P → W j), Continuous v → ObsCont π j w →
      (∀ m, ‖(v m, w m)‖ ≤ r) → ObsCont π (j + 1) fun m => (S m).g j (v m, w m))
    {w₀ : P → W 0} (hw₀ : ObsCont π 0 w₀) (hw : ∀ m, ‖w₀ m‖ ≤ rho β δ θ R) :
    Continuous fun m => (S m).stableMap (w₀ m) := by
  have hθ := hc.theta_pos
  have h1K := hc.one_sub_contr_pos
  have hEinv := continuous_Einv_apply S (fun m => (hS m).norm_Einv_le) hE
  set Nb := rho β δ θ R / (1 - contr β δ γ θ R) with hNb
  have hpN : ∀ n m, WBound θ ((S m).picard (w₀ m) n) Nb := fun n m =>
    (((hS m).fixed hc (hw m)).2.2.2 n).mono (div_le_div_of_nonneg_right (hw m) h1K.le) hθ.le
  have hfN : ∀ m, WBound θ ((S m).fixedSeq (w₀ m)) Nb := fun m =>
    ((hS m).fixed hc (hw m)).1.mono (div_le_div_of_nonneg_right (hw m) h1K.le) hθ.le
  have hvOf : ∀ b : P → ∀ j, W j, (∀ i, ObsCont π i (fun m => b m i)) →
      (∀ m, WBound θ (b m) Nb) → ∀ j, Continuous fun m => (S m).vOf (b m) j := by
    intro b hb hbN j
    refine Continuous.neg (continuous_tsum (fun k => ?_)
      ((summable_geometric_of_lt_one hθ.le hc.theta_lt).mul_left (β * Nb * θ ^ j))
      (fun k m => (hS m).norm_term_le (hbN m) j k))
    exact continuous_pow_clm_apply (fun m => (S m).Einv) (fun m => (hS m).norm_Einv_le) hEinv _
      (hB (j + k) (fun m => b m (j + k)) (hb _)
        ⟨Nb * θ ^ (j + k), fun m => hbN m (j + k)⟩)
  have hpc : ∀ n j, ObsCont π j fun m => (S m).picard (w₀ m) n j := by
    intro n
    induction n with
    | zero =>
      intro j i
      simp only [System.picard_zero, Pi.zero_apply]
      exact continuous_const
    | succ n ih =>
      intro j
      cases j with
      | zero => simpa [System.picard_succ] using hw₀
      | succ j =>
        simp only [System.picard_succ, System.F_succ]
        refine (hD j _ (ih j) ⟨Nb * θ ^ j, fun m => hpN n m j⟩).add ?_
        refine hg j _ _ (hvOf _ ih (hpN n) j) (ih j) (fun m => ?_)
        exact ((hS m).pair_le_R hc (((hS m).fixed hc (hw m)).2.2.2 n)
          (hc.cst_mul_le (norm_nonneg _) (hw m)) j).trans hc.R_le
  have hfc : ∀ j, ObsCont π j fun m => (S m).fixedSeq (w₀ m) j := by
    intro j i
    have hu : Tendsto (fun n => ‖π j i‖ * (rho β δ θ R * contr β δ γ θ R ^ n /
        (1 - contr β δ γ θ R) * θ ^ j)) atTop (𝓝 0) := by
      simpa using (hc.tendsto_rate j).const_mul ‖π j i‖
    refine (tendstoUniformlyOn_univ.1 (tendstoUniformlyOn_of_dist_le hu
      (fun n m _ => ?_))).continuous (Frequently.of_forall fun n => hpc n j i)
    rw [dist_eq_norm, ← map_sub]
    refine ((π j i).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have := (hS m).dist_picard_fixedSeq_le hc (hw m) n j
    rw [dist_eq_norm] at this
    exact this
  exact hvOf _ hfc hfN 0

end Flow
