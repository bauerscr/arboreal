import Ward.ObsLimitCorr

/-!
# Point independence of the infinite-volume single-point couplings

For `z ∈ ℕ^d`, `|b₀| ≤ λ̄`:

* `GamA_eq_GamB`: `GamA(m², b₀) = GamB(m², b₀, z)` for all `m² ≥ 0`.  At `m² > 0` both are
  `lim_N ⟨ψ̄₀ψ₀⟩_N` (translation invariance; `avg_pbp_tendsto`, `avg_pbp_tendsto_B`); at
  `m² = 0` by continuity (`GamA_cont`, `GamB_cont`).
* `LamA_eq_LamB`: `LamA(0, b₀) = LamB(0, b₀, z)`.  On `Λ_N` at the pair
  `(ctr_N, prj z)`, translation invariance of `𝔼[Z₀ ψ̄ψ]` gives the exact identity
  `γ_a U + λ̃_a τ + ε(K_a) = γ_b U + λ̃_b τ + ε(K_b)` (`U = 1 + k⁰ + ã t_N`, `τ = t_N/|Λ|`), valid
  for every `m² > 0` without any non-degeneracy condition.  Dividing by `τ` and letting
  `m² ↓ 0` at fixed `N` (`t_N → ∞`) gives
  `|λ_{a,N} - λ_{b,N}| ≤ |γ_{a,N} - γ_{b,N}| |ã_N| |Λ| + 2 e_N` at `m² = 0` (`lam_diff_zero`);
  here `|γ_{a,N} - γ_{b,N}| = O(L^{-(d-2)N})` (as `GamA = GamB` at `m² = 0`) and
  `|ã_N| |Λ| = O(|b₀| L^{(d-2-κ)N})`, so the right side is `O(L^{-κN})`, and `N → ∞`.

No input from `cor:anm0` is needed.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Metric Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

variable (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) (hd : 1 ≤ d) {Cs : ℝ} (hCs : 0 ≤ Cs)
  (hS : StepBd d L A ℓ₀ V₀c lbar C κ Cs)
include H hd hCs hS

/-- Eventually (in `N`) `z` lies in `[0, L^{N-2})^d`. -/
theorem ev_small {z : Zd d} (hz0 : ∀ i, 0 ≤ z i) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ ∀ i, z i < ((L ^ (N - 2) : ℕ) : ℤ) := by
  have hL3 := three_le_L H
  filter_upwards [eventually_ge_atTop (2 + supNormZ z)] with N hN
  exact ⟨by omega, lt_pow_of_le_supNormZ (by omega) hz0 (by omega)⟩

theorem small_facts {z : Zd d} (hz0 : ∀ i, 0 ≤ z i) {N : ℕ} (hN : 2 ≤ N)
    (hz : ∀ i, z i < ((L ^ (N - 2) : ℕ) : ℤ)) :
    (prj z : Lam d L N) - ctr d L N ≠ 0 ∧
      ctr d L N + ((prj z : Lam d L N) - ctr d L N) = prj z ∧
      redZ N (prj z : Lam d L N) = z := by
  have hL3 := three_le_L H
  have hle : L ^ (N - 2) ≤ L ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨sub_ne_zero.2 (prj_ne_ctr hd hL3 hN hz0 hz), by abel, redZ_prj_of hz0 fun i =>
    (hz i).trans_le (by exact_mod_cast hle)⟩

/-- `GamA` is continuous in `m² ≥ 0` (`|b₀| ≤ λ̄`). -/
theorem GamA_cont (hd3 : 3 ≤ d) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) :
    ContinuousOn (fun m => GamA d L V₀c lbar m b₀) (Set.Ici 0) := by
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  have hU : TendstoUniformlyOn (fun (N : ℕ) (m : ℝ) =>
      gamA2 d L N m (V₀c m b₀) (lbar : ℂ) (ctr d L N)) (fun m => GamA d L V₀c lbar m b₀) atTop
      (Set.Ici 0) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht := (tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ) - 2)
      (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd3); linarith)).const_mul
        (K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) / (rho d L * lbar))
    rw [mul_zero] at ht
    filter_upwards [(tendsto_order.1 ht).2 ε hε, eventually_ge_atTop 2] with N hN hN2 m hm
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt (gamA2_rate H hd hCs hS hd3 hm hb₀ hN2
      (ctr_ne_zero hd hL3 hN2).symm) hN
  exact hU.continuousOn (Frequently.of_forall fun N => H.fd.gamA2_cont hd hb₀ _ _)

/-- `GamB z` is continuous in `m² ≥ 0` (`|b₀| ≤ λ̄`, `z ∈ ℕ^d`). -/
theorem GamB_cont (hd3 : 3 ≤ d) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {z : Zd d} (hz0 : ∀ i, 0 ≤ z i) :
    ContinuousOn (fun m => GamB d L V₀c lbar m b₀ z) (Set.Ici 0) := by
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  have hU : TendstoUniformlyOn (fun (N : ℕ) (m : ℝ) =>
      gamB2 d L N m (V₀c m b₀) (lbar : ℂ) ((prj z : Lam d L N) - ctr d L N))
      (fun m => GamB d L V₀c lbar m b₀ z) atTop (Set.Ici 0) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht := (tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ) - 2)
      (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd3); linarith)).const_mul
        (K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) / (rho d L * lbar))
    rw [mul_zero] at ht
    filter_upwards [(tendsto_order.1 ht).2 ε hε, ev_small H hd hCs hS hz0] with N hN hN2 m hm
    obtain ⟨hx, hadd, hred⟩ := small_facts H hd hCs hS hz0 hN2.1 hN2.2
    have := gamB2_rate H hd hCs hS hd3 hm hb₀ hN2.1 hx
    rw [hadd, hred] at this
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt this hN
  exact hU.continuousOn (Frequently.of_forall fun N => H.fd.gamB2_cont hd hb₀ _ _)

/-- **`⟨ψ̄₀ψ₀⟩_{Λ_N} → γ^{(2)}_{b,∞}(z)`** at `m² > 0`. -/
theorem avg_pbp_tendsto_B (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 < msq) {b₀ : ℂ}
    (hb₀ : ‖b₀‖ ≤ lbar) {z : Zd d} (hz0 : ∀ i, 0 ≤ z i) :
    Tendsto (fun N => avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
      (psibar (0 : Lam d L N) * psi (0 : Lam d L N))) atTop
      (𝓝 (GamB d L V₀c lbar msq b₀ z)) := by
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  obtain ⟨C1, hC1, h1pt⟩ := PtCorr.prop_1pt_of hd3 H.fd
  have hκ := H.fd.κ_pos
  obtain ⟨bd, hbd_def⟩ : ∃ bd : ℕ → ℝ, bd = fun N : ℕ =>
    K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) / (rho d L * lbar) *
      (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) +
    2 * ((1 + C1 * ‖b₀‖) * (1 / (msq * Fintype.card (Lam d L N))) +
      C1 * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
        (L : ℝ) ^ (-(κ * N)) * (1 / (msq * Fintype.card (Lam d L N))))) := ⟨_, rfl⟩
  have hbd : Tendsto bd atTop (𝓝 0) := by
    have t1 := tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ) - 2)
      (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd3); linarith)
    have t2 := tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ) - 2 + κ)
      (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd3); linarith)
    have t3 := tendsto_rpow_neg_mul (L := L) hL2 hκ
    have t4 := tendsto_inv_card (d := d) hd hL2 hmsq
    have := ((t1.const_mul (K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) /
      (rho d L * lbar))).add (((t4.const_mul (1 + C1 * ‖b₀‖)).add
      ((t2.add (t3.mul t4)).const_mul (C1 * ‖b₀‖))).const_mul 2))
    rw [hbd_def]; simpa using this
  have hev1 : ∀ᶠ N : ℕ in atTop, 1 ≤ msq * (L : ℝ) ^ (2 * N) := by
    have : Tendsto (fun N : ℕ => msq * (L : ℝ) ^ (2 * N)) atTop atTop := by
      refine Tendsto.const_mul_atTop hmsq ?_
      have h1 : Tendsto (fun N : ℕ => ((L : ℝ) ^ 2) ^ N) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by
          have : (2 : ℝ) ≤ L := by exact_mod_cast hL2
          nlinarith)
      exact h1.congr fun N => by rw [← pow_mul]
    exact this.eventually_ge_atTop 1
  have hev2 : ∀ᶠ N : ℕ in atTop, (C * lbar + (ℓ₀ ^ 2)⁻¹ * (C * (1 + lbar))) * ‖b₀‖ *
      (L : ℝ) ^ (-(κ * N)) ≤ 1 / 2 := by
    have := (tendsto_rpow_neg_mul (L := L) hL2 hκ).const_mul
      ((C * lbar + (ℓ₀ ^ 2)⁻¹ * (C * (1 + lbar))) * ‖b₀‖)
    rw [mul_zero] at this
    exact (tendsto_order.1 this).2 (1 / 2) (by norm_num) |>.mono fun N h => h.le
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hbd
  filter_upwards [hev1, hev2, ev_small H hd hCs hS hz0] with N hm hu2 hN
  obtain ⟨hx, hadd, hred⟩ := small_facts H hd hCs hS hz0 hN.1 hN.2
  have hu : ‖Suscept.utN d L N msq (V₀c msq b₀)‖ ≤ 1 / 2 :=
    (Psi4.utN_le_of_mass hd H.fd hmsq hm hb₀).trans hu2
  have hu0 : 1 + Suscept.utN d L N msq (V₀c msq b₀) ≠ 0 := by
    intro h
    have : Suscept.utN d L N msq (V₀c msq b₀) = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hu; norm_num at hu
  have hu1 : 1 / 2 ≤ ‖1 + Suscept.utN d L N msq (V₀c msq b₀)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-Suscept.utN d L N msq (V₀c msq b₀))
    rw [sub_neg_eq_add, norm_one, norm_neg] at this
    linarith
  obtain ⟨-, ⟨hlam, -, E, hE, havg⟩⟩ := h1pt N msq b₀ ((prj z : Lam d L N) - ctr d L N)
    (by have := hN.1; omega) hmsq hb₀ hx hu0
  have hg := gamB2_rate H hd hCs hS hd3 hmsq.le hb₀ hN.1 hx
  rw [hadd, hred] at hg
  have hτ := norm_tau_le (d := d) (L := L) (N := N) hd hmsq
  have hlam' : ‖lamB2 d L N msq (V₀c msq b₀) lbar ((prj z : Lam d L N) - ctr d L N)‖ ≤
      1 + C1 * ‖b₀‖ := by
    calc _ = ‖(lamB2 d L N msq (V₀c msq b₀) lbar ((prj z : Lam d L N) - ctr d L N) - 1) + 1‖ := by
          ring_nf
      _ ≤ ‖lamB2 d L N msq (V₀c msq b₀) lbar ((prj z : Lam d L N) - ctr d L N) - 1‖ +
          ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C1 * ‖b₀‖ + 1 := by rw [norm_one]; linarith
      _ = 1 + C1 * ‖b₀‖ := by ring
  have hq : ‖(lamB2 d L N msq (V₀c msq b₀) lbar ((prj z : Lam d L N) - ctr d L N) *
      tau d L N msq + E) / (1 + Suscept.utN d L N msq (V₀c msq b₀))‖ ≤
      2 * ((1 + C1 * ‖b₀‖) * (1 / (msq * Fintype.card (Lam d L N))) +
        C1 * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
          (L : ℝ) ^ (-(κ * N)) * (1 / (msq * Fintype.card (Lam d L N))))) := by
    rw [norm_div]
    have hpos : 0 < ‖1 + Suscept.utN d L N msq (V₀c msq b₀)‖ := by linarith
    rw [div_le_iff₀ hpos]
    have h1 : ‖lamB2 d L N msq (V₀c msq b₀) lbar ((prj z : Lam d L N) - ctr d L N) *
        tau d L N msq + E‖ ≤
        (1 + C1 * ‖b₀‖) * (1 / (msq * Fintype.card (Lam d L N))) +
          C1 * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
            (L : ℝ) ^ (-(κ * N)) * (1 / (msq * Fintype.card (Lam d L N)))) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul hlam' hτ (norm_nonneg _) (by positivity)
      · refine hE.trans (le_of_eq ?_); ring
    have h0 : 0 ≤ (1 + C1 * ‖b₀‖) * (1 / (msq * Fintype.card (Lam d L N))) +
        C1 * ‖b₀‖ * ((L : ℝ) ^ (-(((d : ℝ) - 2 + κ) * N)) +
          (L : ℝ) ^ (-(κ * N)) * (1 / (msq * Fintype.card (Lam d L N)))) := by
      have := Suscept.card_lam_pos (d := d) (L := L) N
      positivity
    nlinarith
  calc ‖avg (Suscept.Cov d L N msq) (VE (V₀c msq b₀) univ)
        (psibar (0 : Lam d L N) * psi (0 : Lam d L N)) - GamB d L V₀c lbar msq b₀ z‖
      = ‖(gamB2 d L N msq (V₀c msq b₀) lbar ((prj z : Lam d L N) - ctr d L N) -
            GamB d L V₀c lbar msq b₀ z) +
          (lamB2 d L N msq (V₀c msq b₀) lbar ((prj z : Lam d L N) - ctr d L N) *
            tau d L N msq + E) / (1 + Suscept.utN d L N msq (V₀c msq b₀))‖ := by
        rw [havg]; ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ bd N := by rw [hbd_def]; exact add_le_add hg hq

/-- **`γ^{(2)}_{a,∞} = γ^{(2)}_{b,∞}(z)`** for all `m² ≥ 0`. -/
theorem GamA_eq_GamB (hd3 : 3 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar)
    {z : Zd d} (hz0 : ∀ i, 0 ≤ z i) :
    GamA d L V₀c lbar msq b₀ = GamB d L V₀c lbar msq b₀ z := by
  have hpos : ∀ m : ℝ, 0 < m → GamA d L V₀c lbar m b₀ = GamB d L V₀c lbar m b₀ z := fun m hm =>
    tendsto_nhds_unique (avg_pbp_tendsto H hCs hS hd3 hm hb₀)
      (avg_pbp_tendsto_B H hd hCs hS hd3 hm hb₀ hz0)
  rcases hmsq.lt_or_eq with h | h
  · exact hpos msq h
  · subst h
    have hA := (GamA_cont H hd hCs hS hd3 hb₀ 0 Set.self_mem_Ici).tendsto.mono_left
      (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    have hB := (GamB_cont H hd hCs hS hd3 hb₀ hz0 0 Set.self_mem_Ici).tendsto.mono_left
      (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    refine tendsto_nhds_unique hA (hB.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with m hm
    exact (hpos m hm).symm

/-! ### The `λ` slot at `m² = 0` -/

omit hCs hS in
/-- Translation invariance at the level of the numerators: `ε(Z̃_a) = ε(Z̃_b)` (Case (2)). -/
theorem eps_ZtO_a_eq_b {N : ℕ} (hN : 1 ≤ N) {msq : ℝ} (hmsq : 0 < msq) (V₀ : Vcoup) (l₀ : ℂ)
    (a x : Lam d L N) :
    ε ((ZtO d L .two N msq V₀ (initObs .two l₀) a (a + x) : SA .two (Lam d L N)).a) =
      ε ((ZtO d L .two N msq V₀ (initObs .two l₀) a (a + x) : SA .two (Lam d L N)).b) := by
  show ε (((eu d L N msq V₀ • Gobs d L .two N msq V₀ l₀ a (a + x) : OE .two (Lam d L N))) :
      SA .two (Lam d L N)).a = ε (((eu d L N msq V₀ • Gobs d L .two N msq V₀ l₀ a (a + x) :
      OE .two (Lam d L N))) : SA .two (Lam d L N)).b
  simp only [Subalgebra.coe_smul, SA.smul_a, SA.smul_b, map_smul, smul_eq_mul]
  have := omega_Z0_transl (msq := msq) hmsq hN V₀ x (psibar a * psi a)
  rw [map_mul, autAlg_psibar, autAlg_psi] at this
  simp only [Equiv.coe_addRight] at this
  rw [ε_Gobs_two_a, ε_Gobs_two_b, this]

theorem tendsto_card_div_tN (hL : 1 ≤ L) (N : ℕ) :
    Tendsto (fun m : ℝ => (Fintype.card (Lam d L N) : ℝ) / Suscept.tNN d L N m) (𝓝[>] 0)
      (𝓝 0) := by
  obtain ⟨K, hK⟩ := tN_sub_inv (P := stdPt) hd
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set n : ℝ := (Fintype.card (Lam d L N) : ℝ)
  have hn : 0 < n := Suscept.card_lam_pos N
  set B : ℝ := (|K| + 1) * (L : ℝ) ^ (2 * N) with hB
  have hB0 : 0 < B := by positivity
  have h2 : Tendsto (fun m : ℝ => 2 * n * m) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun m : ℝ => 2 * n * m) (𝓝 0) (𝓝 (2 * n * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [self_mem_nhdsWithin] with m hm
    exact div_nonneg hn.le (tN_pos stdPt hm (by linarith) N).le
  · have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ), m < 1 / (2 * B) := by
      have : Set.Iio (1 / (2 * B)) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by positivity)
      exact nhdsWithin_le_nhds this
    filter_upwards [self_mem_nhdsWithin, hev] with m hm hmB
    have hm0 : (0 : ℝ) < m := hm
    obtain ⟨-, h2'⟩ := hK m hm0 L hL1 N
    have hKB : K * (L : ℝ) ^ (2 * N) ≤ B := by
      rw [hB]
      have : K ≤ |K| + 1 := by have := le_abs_self K; linarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hmB' : 2 * B * m < 1 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * B)).1 hmB; linarith
    have ht : 1 / (2 * m) ≤ Suscept.tNN d L N m := by
      show 1 / (2 * m) ≤ FRD.tN stdPt d m (L : ℝ) N
      have h3 : 1 / m - B ≤ FRD.tN stdPt d m (L : ℝ) N := by linarith
      have h4 : 1 / (2 * m) ≤ 1 / m - B := by
        rw [div_le_iff₀ (by positivity)]
        have : (1 / m - B) * (2 * m) = 2 - 2 * B * m := by field_simp
        rw [this]; linarith
      linarith
    have htpos : 0 < Suscept.tNN d L N m := lt_of_lt_of_le (by positivity) ht
    rw [div_le_iff₀ htpos]
    have : 1 ≤ 2 * m * Suscept.tNN d L N m := by
      have := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 2 * m)
      rwa [mul_one_div_cancel (by positivity)] at this
    nlinarith

/-- **The key finite-volume inequality at `m² = 0`**: at the pair `(ctr_N, ctr_N + x)`, `x ≠ 0`,
`|λ_{a,N} - λ_{b,N}|/λ̄ ≤ |γ_{a,N} - γ_{b,N}|/λ̄ · |ã_N| |Λ| + 2 e_N/λ̄`,
`e_N = C λ̄ |b₀| L^{-κN}`. -/
theorem lam_diff_zero (hd2 : 2 ≤ d) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ} (hN : 1 ≤ N) {x : Lam d L N}
    (hx : x ≠ 0) :
    ‖lamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - lamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x‖ ≤
      ‖gamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - gamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x‖ *
          (‖Suscept.atN d L N 0 (V₀c 0 b₀)‖ * Fintype.card (Lam d L N)) +
        2 * (C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N))) / lbar := by
  have hd2L : 2 ^ (d + 3) ≤ L := H.fd.hL8
  have hL1 : 1 ≤ L := by have := three_le_L H; omega
  have hlb := H.fd.lbar_pos
  have hC0 := H.fd.C_nonneg
  have hl : (lbar : ℂ) ≠ 0 := by exact_mod_cast hlb.ne'
  have hb : ctr d L N + x ≠ ctr d L N := ctr_add_ne H hd hCs hS hx
  set n : ℝ := (Fintype.card (Lam d L N) : ℝ) with hn_def
  have hn : 0 < n := Suscept.card_lam_pos N
  set eN := C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N)) with heN
  have heN0 : 0 ≤ eN := by
    have := Real.rpow_nonneg (Nat.cast_nonneg L) (-(κ * N)); rw [heN]; positivity
  -- the bound for `m > 0`
  have hpos : ∀ m : ℝ, 0 < m →
      ‖lamA2 d L N m (V₀c m b₀) (lbar : ℂ) x - lamB2 d L N m (V₀c m b₀) (lbar : ℂ) x‖ ≤
        ‖gamA2 d L N m (V₀c m b₀) (lbar : ℂ) x - gamB2 d L N m (V₀c m b₀) (lbar : ℂ) x‖ *
            (‖1 + Suscept.kN0 d L N m (V₀c m b₀)‖ * (n / Suscept.tNN d L N m) +
              ‖Suscept.atN d L N m (V₀c m b₀)‖ * n) +
          (2 * eN + 2 * ℓ₀ ^ 2 * eN * (n / Suscept.tNN d L N m)) / lbar := by
    intro m hm
    have hgood := H.fd.good N m hm.le
    have ht : 0 < Suscept.tNN d L N m := tN_pos stdPt hm (by positivity) N
    have hτ : tau d L N m = ((Suscept.tNN d L N m / n : ℝ) : ℂ) := rfl
    have hτ0 : (tau d L N m) ≠ 0 := by
      rw [hτ]; exact_mod_cast (div_pos ht hn).ne'
    have fa := ε_ZtO_a_two (V₀c m b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + x) hd hd2L hN hm hgood
    have fb := ε_ZtO_b_two (V₀c m b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + x) hd hd2L hN hm hgood
    have hab := eps_ZtO_a_eq_b H hd hN hm (V₀c m b₀) (lbar : ℂ) (ctr d L N) x
    rw [fa, fb] at hab
    have hKN := (H.fd.obs .two N m (lbar : ℂ) b₀ (ctr d L N + x) hm.le
      (by rw [norm_lbar H]; exact hb₀) (le_of_eq (norm_lbar H)) hb N le_rfl).2
    rw [norm_lbar H] at hKN
    obtain ⟨k1, k2, k3, k4, -⟩ := kTwo_bounds H.fd.hℓ₀ H.fd.hA1 heN0 (initObs .two (lbar : ℂ)) hKN
    have hℓN : ellj d (L : ℝ) ℓ₀ N ^ 2 ≤ ℓ₀ ^ 2 := by
      rw [ellj_sq]
      have := pow_le_one₀ (n := N) (rho_nonneg d L) (rho_le_one hd2 L)
      have h3 : 0 ≤ ℓ₀ ^ 2 := sq_nonneg _
      calc ℓ₀ ^ 2 * rho d L ^ N ≤ ℓ₀ ^ 2 * 1 := mul_le_mul_of_nonneg_left this h3
        _ = ℓ₀ ^ 2 := mul_one _
    -- names
    set la := laOf .two (VoN d L .two N m (V₀c m b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
      (ctr d L N + x))
    set lb := lbOf .two (VoN d L .two N m (V₀c m b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
      (ctr d L N + x))
    set lta := lamtA d L N m (V₀c m b₀) (initObs .two (lbar : ℂ)) (ctr d L N) (ctr d L N + x)
    set ltb := lamtB d L N m (V₀c m b₀) (initObs .two (lbar : ℂ)) (ctr d L N) (ctr d L N + x)
    set ga := gaN d L .two N m (V₀c m b₀) (initObs .two (lbar : ℂ)) (ctr d L N) (ctr d L N + x)
    set gb := gbN d L .two N m (V₀c m b₀) (initObs .two (lbar : ℂ)) (ctr d L N) (ctr d L N + x)
    set Ka := ε ((KNO d L .two N m (V₀c m b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
      (ctr d L N + x) : SA .two (Lam d L N)).a)
    set Kb := ε ((KNO d L .two N m (V₀c m b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
      (ctr d L N + x) : SA .two (Lam d L N)).b)
    set U := 1 + Suscept.utN d L N m (V₀c m b₀)
    set τ := tau d L N m
    have hU : U = (1 + Suscept.kN0 d L N m (V₀c m b₀)) +
        Suscept.atN d L N m (V₀c m b₀) * (Suscept.tNN d L N m : ℂ) := by
      show 1 + (Suscept.kN0 d L N m (V₀c m b₀) +
        Suscept.atN d L N m (V₀c m b₀) * (Suscept.tNN d L N m : ℂ)) = _
      ring
    have hdiff : lta - ltb = ((gb - ga) * U + (Kb - Ka)) / τ := by
      field_simp; linear_combination hab
    have hUτ : ‖U / τ‖ ≤ ‖1 + Suscept.kN0 d L N m (V₀c m b₀)‖ * (n / Suscept.tNN d L N m) +
        ‖Suscept.atN d L N m (V₀c m b₀)‖ * n := by
      have e : U / τ = (1 + Suscept.kN0 d L N m (V₀c m b₀)) * ((n / Suscept.tNN d L N m : ℝ) : ℂ) +
          Suscept.atN d L N m (V₀c m b₀) * (n : ℂ) := by
        have htne : (Suscept.tNN d L N m : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
        rw [hU, hτ]; push_cast; field_simp
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hn.le ht.le),
        Complex.norm_real, Real.norm_of_nonneg hn.le]
    have hτinv : ‖1 / τ‖ = n / Suscept.tNN d L N m := by
      rw [hτ, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (div_nonneg ht.le hn.le)]
      field_simp
    have hKab : ‖Kb - Ka‖ ≤ 2 * ℓ₀ ^ 2 * eN := by
      have := mul_le_mul_of_nonneg_right hℓN heN0
      refine (norm_sub_le _ _).trans ?_
      linarith
    have hD : ‖la - lb‖ ≤ 2 * eN + ‖ga - gb‖ * (‖1 + Suscept.kN0 d L N m (V₀c m b₀)‖ *
        (n / Suscept.tNN d L N m) + ‖Suscept.atN d L N m (V₀c m b₀)‖ * n) +
        2 * ℓ₀ ^ 2 * eN * (n / Suscept.tNN d L N m) := by
      have e : la - lb = (la - lta) - (lb - ltb) + ((gb - ga) * (U / τ) + (Kb - Ka) * (1 / τ)) := by
        rw [show (gb - ga) * (U / τ) + (Kb - Ka) * (1 / τ) = lta - ltb by
          rw [hdiff]; field_simp]
        ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add (norm_sub_le _ _) ((norm_add_le _ _).trans (add_le_add
        (norm_mul_le _ _) (norm_mul_le _ _)))).trans ?_
      rw [hτinv, norm_sub_rev gb ga]
      have := mul_le_mul_of_nonneg_left hUτ (norm_nonneg (ga - gb))
      have := mul_le_mul_of_nonneg_right hKab (div_nonneg hn.le ht.le)
      linarith
    have e1 : lamA2 d L N m (V₀c m b₀) (lbar : ℂ) x - lamB2 d L N m (V₀c m b₀) (lbar : ℂ) x =
        (la - lb) / lbar := by rw [lamA2, lamB2, sub_div]
    have e2 : gamA2 d L N m (V₀c m b₀) (lbar : ℂ) x - gamB2 d L N m (V₀c m b₀) (lbar : ℂ) x =
        (ga - gb) / lbar := by rw [gamA2, gamB2, sub_div]
    rw [e1, e2, norm_div, norm_div, norm_lbar H, div_le_iff₀ hlb]
    have hQ : 0 ≤ ‖1 + Suscept.kN0 d L N m (V₀c m b₀)‖ * (n / Suscept.tNN d L N m) +
        ‖Suscept.atN d L N m (V₀c m b₀)‖ * n := by positivity
    calc ‖la - lb‖ ≤ _ := hD
      _ = (‖ga - gb‖ / lbar * (‖1 + Suscept.kN0 d L N m (V₀c m b₀)‖ *
          (n / Suscept.tNN d L N m) + ‖Suscept.atN d L N m (V₀c m b₀)‖ * n) +
          (2 * eN + 2 * ℓ₀ ^ 2 * eN * (n / Suscept.tNN d L N m)) / lbar) * lbar := by
        field_simp; ring
  -- the limit `m ↓ 0`
  have hcv := H.fd.cv hb₀
  obtain ⟨-, -, hk0, -, hat, -⟩ := Suscept.prop_ZNN_cont (N := N) hd hd2L subset_rfl hcv
    (fun m hm => H.fd.good N m hm)
  have hlim : ∀ {f : ℝ → ℂ}, ContinuousOn f (Set.Ici 0) → Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    fun hf => (hf 0 Set.self_mem_Ici).tendsto.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hA := hlim (H.fd.lamA2_cont hd hb₀ (lbar : ℂ) x)
  have hB := hlim (H.fd.lamB2_cont hd hb₀ (lbar : ℂ) x)
  have hgA := hlim (H.fd.gamA2_cont hd hb₀ (lbar : ℂ) x)
  have hgB := hlim (H.fd.gamB2_cont hd hb₀ (lbar : ℂ) x)
  have hK := hlim hk0
  have hT := hlim hat
  have hnt := tendsto_card_div_tN H hd hCs hS hL1 N (d := d)
  have hF : Tendsto (fun m => ‖lamA2 d L N m (V₀c m b₀) (lbar : ℂ) x -
      lamB2 d L N m (V₀c m b₀) (lbar : ℂ) x‖) (𝓝[>] 0)
      (𝓝 ‖lamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - lamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x‖) :=
    (hA.sub hB).norm
  have hG : Tendsto (fun m => ‖gamA2 d L N m (V₀c m b₀) (lbar : ℂ) x -
        gamB2 d L N m (V₀c m b₀) (lbar : ℂ) x‖ *
          (‖1 + Suscept.kN0 d L N m (V₀c m b₀)‖ * (n / Suscept.tNN d L N m) +
            ‖Suscept.atN d L N m (V₀c m b₀)‖ * n) +
        (2 * eN + 2 * ℓ₀ ^ 2 * eN * (n / Suscept.tNN d L N m)) / lbar) (𝓝[>] 0)
      (𝓝 (‖gamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - gamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x‖ *
          (‖1 + Suscept.kN0 d L N 0 (V₀c 0 b₀)‖ * 0 + ‖Suscept.atN d L N 0 (V₀c 0 b₀)‖ * n) +
        (2 * eN + 2 * ℓ₀ ^ 2 * eN * 0) / lbar)) :=
    ((hgA.sub hgB).norm.mul ((((tendsto_const_nhds.add hK).norm).mul hnt).add
      (hT.norm.mul tendsto_const_nhds))).add
      ((tendsto_const_nhds.add ((tendsto_const_nhds.mul tendsto_const_nhds).mul hnt)).div_const _)
  have := le_of_tendsto_of_tendsto hF hG (by
    filter_upwards [self_mem_nhdsWithin] with m hm using hpos m hm)
  refine this.trans (le_of_eq ?_)
  simp only [mul_zero, add_zero, zero_add]

/-- `|Λ_N| L^{-(d-2)N} L^{-(2+κ)N} = L^{-κN}`. -/
theorem card_rpow (N : ℕ) :
    (Fintype.card (Lam d L N) : ℝ) * ((L : ℝ) ^ (-(((d : ℝ) - 2) * N)) *
      (L : ℝ) ^ (-((2 + κ) * N))) = (L : ℝ) ^ (-(κ * N)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [Suscept.card_lam, Nat.cast_pow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hL0,
    ← Real.rpow_add hL0]
  congr 1
  push_cast; ring

/-- **Point independence: `λ^{(2)}_{a,∞} = λ^{(2)}_{b,∞}(z)` at `m² = 0`** (`z ∈ ℕ^d`, `|b₀| ≤ λ̄`). -/
theorem LamA_eq_LamB (hd3 : 3 ≤ d) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {z : Zd d}
    (hz0 : ∀ i, 0 ≤ z i) :
    LamA d L V₀c lbar 0 b₀ = LamB d L V₀c lbar 0 b₀ z := by
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  have hlb := H.fd.lbar_pos
  have hκ := H.fd.κ_pos
  have hC0 := H.fd.C_nonneg
  have hGam := GamA_eq_GamB H hd hCs hS hd3 le_rfl hb₀ hz0
  obtain ⟨KG, hKG⟩ : ∃ KG : ℝ, KG = K1 lbar C κ Cs L * ℓ₀ ^ 2 * (1 + 1 / (1 - rho d L)) /
      (rho d L * lbar) := ⟨_, rfl⟩
  obtain ⟨Klam, hKlam⟩ : ∃ Klam : ℝ, Klam = 2 * Cs * C / (th L κ ^ 2 * (1 - th L κ)) * ‖b₀‖ := ⟨_, rfl⟩
  obtain ⟨Ka, hKa⟩ : ∃ Ka : ℝ, Ka = (ℓ₀ ^ 2)⁻¹ * C * (1 + lbar) * ‖b₀‖ := ⟨_, rfl⟩
  obtain ⟨bd, hbd_def⟩ : ∃ bd : ℕ → ℝ, bd = fun N : ℕ =>
      2 * Klam * (L : ℝ) ^ (-(κ * N)) + 2 * KG * Ka * (L : ℝ) ^ (-(κ * N)) +
        2 * (C * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * N))) / lbar := ⟨_, rfl⟩
  have hbd : Tendsto bd atTop (𝓝 0) := by
    have t := tendsto_rpow_neg_mul (L := L) hL2 hκ
    have := ((t.const_mul (2 * Klam)).add (t.const_mul (2 * KG * Ka))).add
      ((t.const_mul (C * lbar * ‖b₀‖)).const_mul 2 |>.div_const lbar)
    rw [hbd_def]; simpa using this
  have hle : ∀ᶠ N : ℕ in atTop,
      ‖LamA d L V₀c lbar 0 b₀ - LamB d L V₀c lbar 0 b₀ z‖ ≤ bd N := by
    filter_upwards [ev_small H hd hCs hS hz0] with N hN
    obtain ⟨hx, hadd, hred⟩ := small_facts H hd hCs hS hz0 hN.1 hN.2
    set x := (prj z : Lam d L N) - ctr d L N
    have hrA := lamA2_rate H hd hCs hS le_rfl hb₀ hN.1 hx
    have hrB := lamB2_rate H hd hCs hS le_rfl hb₀ hN.1 hx
    rw [hadd, hred] at hrB
    have hgA := gamA2_rate H hd hCs hS hd3 le_rfl hb₀ hN.1 hx
    have hgB := gamB2_rate H hd hCs hS hd3 le_rfl hb₀ hN.1 hx
    rw [hadd, hred, ← hGam] at hgB
    have hdiff := lam_diff_zero H hd hCs hS (by omega) hb₀ (by have := hN.1; omega) hx
    have hat := Psi4.atN_le (N := N) H.fd le_rfl hb₀
    rw [← hKa] at hat
    have hγ : ‖gamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - gamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x‖ ≤
        2 * KG * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) := by
      rw [← hKG] at hgA hgB
      calc _ = ‖(gamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - GamA d L V₀c lbar 0 b₀) -
            (gamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - GamA d L V₀c lbar 0 b₀)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
        _ ≤ _ := by linarith
    have hn : 0 ≤ (Fintype.card (Lam d L N) : ℝ) := Nat.cast_nonneg _
    have hKG0 : 0 ≤ KG := by
      have hθ1 := th_lt_one hL2 hκ (L := L)
      have hρ1 := rho_lt_one hd3 hL2 (L := L)
      have hρp : 0 < rho d L :=
        Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
      have : 0 < 1 - th L κ := by linarith
      have : 0 < 1 - rho d L := by linarith
      rw [hKG]; unfold K1; positivity
    have hprod : ‖gamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - gamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x‖ *
        (‖Suscept.atN d L N 0 (V₀c 0 b₀)‖ * Fintype.card (Lam d L N)) ≤
        2 * KG * Ka * (L : ℝ) ^ (-(κ * N)) := by
      have hr1 := Real.rpow_nonneg (Nat.cast_nonneg L) (-(((d : ℝ) - 2) * N))
      have hat' : ‖Suscept.atN d L N 0 (V₀c 0 b₀)‖ ≤ Ka * (L : ℝ) ^ (-((2 + κ) * N)) := hat
      calc _ ≤ (2 * KG * (L : ℝ) ^ (-(((d : ℝ) - 2) * N))) *
            (Ka * (L : ℝ) ^ (-((2 + κ) * N)) * Fintype.card (Lam d L N)) :=
            mul_le_mul hγ (mul_le_mul_of_nonneg_right hat' hn) (by positivity) (by positivity)
        _ = 2 * KG * Ka * ((Fintype.card (Lam d L N) : ℝ) *
            ((L : ℝ) ^ (-(((d : ℝ) - 2) * N)) * (L : ℝ) ^ (-((2 + κ) * N)))) := by ring
        _ = _ := by rw [card_rpow H hd hCs hS]
    have hlA : ‖lamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - LamA d L V₀c lbar 0 b₀‖ ≤
        Klam * (L : ℝ) ^ (-(κ * N)) := by rw [hKlam]; exact hrA
    have hlB : ‖lamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - LamB d L V₀c lbar 0 b₀ z‖ ≤
        Klam * (L : ℝ) ^ (-(κ * N)) := by rw [hKlam]; exact hrB
    calc ‖LamA d L V₀c lbar 0 b₀ - LamB d L V₀c lbar 0 b₀ z‖
        = ‖(lamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - LamB d L V₀c lbar 0 b₀ z) -
            (lamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - LamA d L V₀c lbar 0 b₀) +
            (lamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - lamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x)‖ := by
          ring_nf
      _ ≤ ‖lamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - LamB d L V₀c lbar 0 b₀ z‖ +
            ‖lamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - LamA d L V₀c lbar 0 b₀‖ +
            ‖lamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x - lamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) x‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ bd N := by rw [hbd_def]; linarith
  have h0 : ‖LamA d L V₀c lbar 0 b₀ - LamB d L V₀c lbar 0 b₀ z‖ ≤ 0 :=
    ge_of_tendsto hbd hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

end

end Ward
