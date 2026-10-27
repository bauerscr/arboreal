import Flow.FlowDefs

/-!
# Ingredients of Theorem `thm:flow` and Corollary `cor:flow-finvol` (Section `sec:flow`)

The main result `Flow.thm_flow` (Theorem `thm:flow`, Corollary `cor:flow-finvol` and the remark on
`u_N` after it; see its docstring for the list of claims) is stated and proved in `Flow/Main.lean`,
from `Flow.thm_flow_body`, which also gives the reality of `V_0^c` (this needs `Flow/Conj.lean`).
This file contains the ingredients of the proof.

## Proof structure
* `exists_hyp`: the hypotheses `Hyp` (conclusions of `step_deriv`, `step`, `goodCov_Cfrd`,
  `cov_bounds`, `WQ_bounds`) hold for `L ≥ L₀`, `A ≥ A₀(L)`, `ℓ₀² ≥ K L^{d-2+2p_Φ}`, with
  `δ_K = C₀(L^{-d_+} + A^{-η}) ≤ 1/2`.
* `RGsys` (`Flow/RGSystem.lean`) is the dynamical system `e:flowblock`; `RGsys_bounds`,
  `RGsys_analytic`, `RGsys_cont*` verify the hypotheses of the abstract stable manifold theorem
  (`Flow/StableManifold.lean`, `Flow/StableCont.lean`) with `θ = 3/4`, `δ = max(L^{-(d-2)}, δ_K)`.
* `V_0^c(m², b₀) = Vc H m² b₀` is given by the stable manifold map at `w₀ = (b₀, 0)`.
* `flowN_orbit` identifies the torus flows with the orbit; `orbit_K` gives `K_j = O(b₀² θ^j)` by
  induction from `K₀ = 0`; `flow_bounds_fin` handles the last (at most three) steps on each torus
  with `thm:step` (`step_real`), including the last step with `C_N`.

## Deviations from the paper
* The infinite volume space `𝒦_j(ℤ^d)` is realised as compatible families `(K_j^N)_{N ≥ j+3}` of
  torus activities (`KFam`), and the infinite volume flow as the family of torus flows `flowN N`.
  Accordingly `e:flowVK` is stated for the torus flows in the range `j + 3 ≤ N` (claim 1) and, as
  in `cor:flow-finvol`, for all `j ≤ N` (claim 6). `V_j` is proved torus independent for
  `j ≤ N - 2` and `u_{j+1}` for `j + 3 ≤ N` (the paper states `j < N`).
* The decay is `θ^j` with `θ = 3/4 = L^{-κ}`, `κ = log_L(4/3)`; the constants `C, b̄` depend on
  `L, A, ℓ₀` (the paper's `O_L`).
* The stable manifold theorem is our own (not MR2523458, Thm 2.16). Continuity in `m²` is proved
  through the torus projections (`continuous_stableMap_obs`), since the RG map is only known to be
  continuous in `m²` coefficientwise on each torus.
* "Differentiable in `b₀` with bounded derivative" is proved as complex differentiability on the
  disc `|b₀| < b̄` with `|∂_{b₀} z|, |∂_{b₀} y|, |∂_{b₀} a| ≤ C`.
* The mass enters as `m² = max m 0`; all claims are for `m² ≥ 0`.
* `K_{j+1}` is restricted to connected `(j+1)`-polymers (normalised activities) and `K_0 = 0`.
* `Loc` produces no quartic terms, so `b_{j+1} = b_j` exactly (`r̂^b = 0`); `D_j` has norm
  `≤ max(L^{-(d-2)}, C₀(L^{-d_+} + A^{-η}))` (without the factor `b₀` written in the paper).
* The total prefactor constant is `u_N^{tot} = ∑_{j<N} u_{j+1}` (each step is started with
  `u_j = 0`, as in the remark after the proof of `thm:flow`).
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step Metric Filter Topology Coup

variable {d : ℕ}

theorem Vnorm_zero' {L N : ℕ} [NeZero L] (j : ℕ) (ℓ : ℝ) :
    Vnorm (d := d) (L := L) (N := N) j ℓ (0 : Vcoup) = 0 := by
  have := Vnorm_smul (d := d) (L := L) (N := N) j ℓ 0 0
  simpa using this

theorem rpow_neg_dplus_le (hd : 3 ≤ d) {L : ℝ} (hL : 1 ≤ L) :
    L ^ (-dplus d) ≤ (Real.sqrt L)⁻¹ := by
  have h0 : (1 / 2 : ℝ) ≤ dplus d := by
    unfold dplus
    refine le_min ?_ (by norm_num)
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  calc L ^ (-dplus d) ≤ L ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    _ = (Real.sqrt L)⁻¹ := by
        rw [Real.rpow_neg (by linarith), Real.sqrt_eq_rpow]

/-- **The hypotheses `Hyp` hold** for `L ≥ L₀`, `A ≥ A₀(L)`, `ℓ₀² ≥ K L^{d - 2 + 2 p_Φ}`, with
`δ_K = C₀ (L^{-d_+} + A^{-η}) ≤ 1/2`. -/
theorem exists_hyp (hd : 3 ≤ d) : ∃ (L₀ : ℕ) (Kℓ : ℝ), 0 ≤ Kℓ ∧ ∀ (L : ℕ) [NeZero L],
    L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
    ∃ ε C₁ δK Kc Cw : ℝ, Hyp d L A ℓ₀ ε C₁ δK Kc Cw ∧ δK ≤ 1 / 2 := by
  obtain ⟨C₀, η, Ls, hC₀, hη, hsd⟩ := step_deriv hd
  obtain ⟨C₀', η', ν', Lst, hC₀', hη', hν', hst⟩ := step hd
  obtain ⟨Kg, hKg0, hgood⟩ := goodCov_Cfrd hd
  obtain ⟨Kc, hKc, hcov⟩ := cov_bounds hd
  obtain ⟨Cw, hCw, hwq⟩ := WQ_bounds hd
  set Lδ : ℕ := ⌈16 * C₀ ^ 2⌉₊ + 1
  refine ⟨max (max Ls Lst) (max (2 ^ (d + 3) + 8 * d + 1) Lδ), Kg, hKg0, fun L _ hL => ?_⟩
  have hLs : Ls ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLst : Lst ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL8 : 2 ^ (d + 3) + 8 * d + 1 ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLδ : Lδ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  obtain ⟨A₁, hA₁, hA₁'⟩ := hsd L hLs
  obtain ⟨A₂, hA₂, hA₂'⟩ := hst L hLst
  refine ⟨max (max A₁ A₂) ((4 * C₀ + 1) ^ (1 / η)), le_trans hA₁ (le_trans (le_max_left _ _)
    (le_max_left _ _)), fun A hA ℓ₀ hℓ₀ hKℓ => ?_⟩
  have hAA₁ : A₁ ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA
  have hAA₂ : A₂ ≤ A := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA
  have hAη : (4 * C₀ + 1) ^ (1 / η) ≤ A := le_trans (le_max_right _ _) hA
  have hA1 : 1 ≤ A := hA₁.trans hAA₁
  obtain ⟨ε, C₁, hε, hC₁, hsd'⟩ := hA₁' A hAA₁
  obtain ⟨ε₂, hε₂, hst'⟩ := hA₂' A hAA₂
  have hgd : ∀ (N j : ℕ), j + 1 < N → ∀ msq : ℝ, 0 ≤ msq →
      GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Cfrd d L N msq j) :=
    fun N j hj msq hmsq => hgood L (by omega) ℓ₀ hℓ₀ hKℓ N j hj msq hmsq
  refine ⟨ε, C₁, C₀ * ((L : ℝ) ^ (-dplus d) + A ^ (-η)), Kc, Cw, ?_, ?_⟩
  · refine
      { hd := hd
        hL := by omega
        hA := hA1
        hℓ₀ := hℓ₀
        hε := hε
        hC₁ := hC₁
        hδK := by positivity
        hKc := hKc
        hCw := hCw
        good := hgd
        zero := fun N j hj msq hmsq => ?_
        lip := fun N j hj msq hmsq => (hsd' N j (by omega) ℓ₀ hℓ₀ _ (hgd N j hj msq hmsq)).2.1
        rem := fun N j hj msq hmsq =>
          (hsd' N j (by omega) ℓ₀ hℓ₀ _ (hgd N j hj msq hmsq)).2.2.2.2
        dK := fun N j hj msq hmsq V' K' hK' => by
          have := (hsd' N j (by omega) ℓ₀ hℓ₀ _ (hgd N j hj msq hmsq)).2.2.1 V' K' hK'
          rwa [if_pos hj] at this
        dV := fun N j hj msq hmsq => (hsd' N j (by omega) ℓ₀ hℓ₀ _ (hgd N j hj msq hmsq)).2.2.2.1
        cov := fun N j hj msq hmsq => hcov L N j hj msq hmsq
        wq := fun N j hj K hK i₀ => hwq L (by omega) N j hj ℓ₀ hℓ₀ A hA1 K hK i₀ }
    have h := (hst' N j (by omega) ℓ₀ hℓ₀ _ (hgd N j hj msq hmsq) 0 0 (InK.zero j)
      (by rw [Vnorm_zero', Knorm_zero, zero_add]; exact zero_le)).2.2
    rw [Vnorm_zero', Knorm_zero] at h
    simpa using h
  · -- `δ_K ≤ 1/2`
    have h1 : C₀ * (L : ℝ) ^ (-dplus d) ≤ 1 / 4 := by
      have hsq : 4 * C₀ ≤ Real.sqrt L := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        have : 16 * C₀ ^ 2 ≤ (Lδ : ℝ) := by
          have := Nat.le_ceil (16 * C₀ ^ 2)
          push_cast [Lδ]; linarith
        nlinarith [(by exact_mod_cast hLδ : (Lδ : ℝ) ≤ L)]
      have hs0 : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
      calc C₀ * (L : ℝ) ^ (-dplus d) ≤ C₀ * (Real.sqrt L)⁻¹ :=
            mul_le_mul_of_nonneg_left (rpow_neg_dplus_le hd hL1) hC₀
        _ ≤ 1 / 4 := by
            rw [← div_eq_mul_inv, div_le_iff₀ hs0]; linarith
    have h2 : C₀ * A ^ (-η) ≤ 1 / 4 := by
      have hA0 : 0 < A := by linarith
      have hb : 0 < 4 * C₀ + 1 := by linarith
      have h3 : A ^ (-η) ≤ (4 * C₀ + 1)⁻¹ := by
        have := Real.rpow_le_rpow (by positivity) hAη (by linarith : 0 ≤ η)
        rw [← Real.rpow_mul hb.le, one_div_mul_cancel hη.ne', Real.rpow_one] at this
        rw [Real.rpow_neg hA0.le]
        exact inv_anti₀ hb this
      calc C₀ * A ^ (-η) ≤ C₀ * (4 * C₀ + 1)⁻¹ := mul_le_mul_of_nonneg_left h3 hC₀
        _ ≤ 1 / 4 := by
            rw [← div_eq_mul_inv, div_le_iff₀ hb]; linarith
    linarith [mul_add C₀ ((L : ℝ) ^ (-dplus d)) (A ^ (-η))]

/-- **One step of the flow in real form** (from `thm:step` and `E:vj`), used for the last steps
of the finite volume flow (Corollary `cor:flow-finvol`): with `v = ‖V‖_j`, `k = ‖K‖_j` and
`v + k ≤ ε'`,
`‖K_{j+1}‖_{j+1} ≤ a_K (k + v² + k²)`, `‖V_{j+1}‖_{j+1} ≤ 2 L^d (v + C_u k)` and
`|u_{j+1}| L^{jd} ≤ v + C_u k`. -/
theorem step_real (hd : 3 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧
    ∀ A : ℝ, A₀ ≤ A → ∃ ε' aK Cu : ℝ, 0 < ε' ∧ 0 ≤ aK ∧ 0 ≤ Cu ∧
    ∀ (N j : ℕ), j < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V : Vcoup) (K : Act d L N), InK j K →
      (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal +
          (Knorm j (ellj d L ℓ₀ j) A K).toReal ≤ ε' →
      (Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (Knext j C V K)).toReal ≤
          aK * ((Knorm j (ellj d L ℓ₀ j) A K).toReal +
            (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal ^ 2 +
            (Knorm j (ellj d L ℓ₀ j) A K).toReal ^ 2) ∧
      (Vnorm (d := d) (L := L) (N := N) (j + 1) (ellj d L ℓ₀ (j + 1)) (uVnext j C V K).2).toReal ≤
          2 * (L : ℝ) ^ d * ((Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal +
            Cu * (Knorm j (ellj d L ℓ₀ j) A K).toReal) ∧
      ‖(uVnext j C V K).1‖ * (L : ℝ) ^ (j * d) ≤
          (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal +
            Cu * (Knorm j (ellj d L ℓ₀ j) A K).toReal := by
  obtain ⟨C₀, η, ν, Lst, hC₀, hη, hν, hst⟩ := step hd
  obtain ⟨Cu, Lu, hCu, hLu, hub⟩ := uVnext_bounds hd
  refine ⟨max Lst Lu, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, hA⟩ := hst L (le_trans (le_max_left _ _) hL)
  refine ⟨A₀, hA₀, fun A hAA => ?_⟩
  obtain ⟨ε, hε, hS⟩ := hA A hAA
  have hA1 : 1 ≤ A := hA₀.trans hAA
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  refine ⟨ε, C₀ * ((L : ℝ) ^ d + 1 + A ^ (-η)) + C₀ * A ^ ν, Cu, hε, by positivity, hCu,
    fun N j hj ℓ₀ hℓ₀ C hC V K hK hsmall => ?_⟩
  have hℓ := ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) hℓ₀ j
  set v := (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal with hv
  set k := (Knorm j (ellj d L ℓ₀ j) A K).toReal with hk
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have ev : Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V = ENNReal.ofReal v :=
    (ENNReal.ofReal_toReal (Vnorm_ne_top hℓ V)).symm
  have ek : Knorm j (ellj d L ℓ₀ j) A K = ENNReal.ofReal k :=
    (ENNReal.ofReal_toReal (Step.Knorm_ne_top hℓ K)).symm
  have hsm : Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V + Knorm j (ellj d L ℓ₀ j) A K ≤
      ENNReal.ofReal ε := by
    rw [ev, ek, ← ENNReal.ofReal_add hv0 hk0]; exact ENNReal.ofReal_le_ofReal hsmall
  obtain ⟨-, -, hK1⟩ := hS N j hj ℓ₀ hℓ₀ C hC V K hK hsm
  obtain ⟨hu, hV', -⟩ := hub L (le_trans (le_max_right _ _) hL) N j hj ℓ₀ hℓ₀ C hC V K A hA1 hK
  set f : ℝ := if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ d with hf
  have hf1 : f ≤ (L : ℝ) ^ d + 1 := by
    rw [hf]; split_ifs
    · linarith [rpow_neg_dplus_le_one hd (by exact_mod_cast NeZero.one_le : 1 ≤ L),
        pow_nonneg (by linarith : (0 : ℝ) ≤ L) d]
    · linarith
  have hf0 : 0 ≤ f := by rw [hf]; split_ifs <;> positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [ev, ek] at hK1
    rw [← ENNReal.ofReal_pow hv0, ← ENNReal.ofReal_pow hk0,
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)] at hK1
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hK1.trans (ENNReal.ofReal_le_ofReal ?_))
    have hAη : 0 ≤ A ^ (-η) := Real.rpow_nonneg (by linarith) _
    have hAν : 0 ≤ A ^ ν := Real.rpow_nonneg (by linarith) _
    have h1 : C₀ * (f + A ^ (-η)) * k ≤ C₀ * ((L : ℝ) ^ d + 1 + A ^ (-η)) * k := by gcongr
    have h2 : 0 ≤ C₀ * ((L : ℝ) ^ d + 1 + A ^ (-η)) * (v ^ 2 + k ^ 2) := by positivity
    have h3 : 0 ≤ C₀ * A ^ ν * k := by positivity
    nlinarith
  · -- the bound on `V_{j+1}`
    have hb : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
        Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
          ((uVnext j C V K).2.eval (blockSet (L := L) (N := N) j b)) ≤
          ENNReal.ofReal (2 * (v + Cu * k)) := by
      intro b hbj
      refine (hV' b hbj).trans (le_of_eq ?_)
      rw [ev, ek, ← ENNReal.ofReal_mul hCu, ← ENNReal.ofReal_add hv0 (by positivity),
        ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    have hvb : Vnorm (d := d) (L := L) (N := N) (j + 1) (ellj d L ℓ₀ (j + 1)) (uVnext j C V K).2 ≤
        ENNReal.ofReal (2 * (L : ℝ) ^ d * (v + Cu * k)) := by
      refine iSup₂_le fun b' _ => ?_
      have hP : IsPolymer j (blockSet (L := L) (N := N) (j + 1) b') :=
        IsPolymer.of_succ (isPolymer_blockSet (L := L) (N := N) (j + 1) b')
      rw [eval_polymer _ hP]
      refine (tNorm_sum_le _ _).trans ?_
      refine (sum_le_sum fun b hbb => hb b (mem_blockIdx_of_mem_blocks hbb)).trans ?_
      rw [sum_const, nsmul_eq_mul]
      have hnb := nb_blockSet_succ_le (L := L) (N := N) j b'
      rw [nb] at hnb
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : (0 : ℝ) ≤ 2 * (v + Cu * k) := by positivity
      calc ((blocks j (blockSet (L := L) (N := N) (j + 1) b')).card : ℝ) * (2 * (v + Cu * k))
          ≤ (L : ℝ) ^ d * (2 * (v + Cu * k)) := by
            gcongr; exact_mod_cast hnb
        _ = 2 * (L : ℝ) ^ d * (v + Cu * k) := by ring
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hvb
  · -- the bound on `u_{j+1}`
    have h := hu 0 (zero_mem_blockIdx j)
    rw [card_blockSet (by omega) (zero_mem_blockIdx j), ev, ek, ← ENNReal.ofReal_mul hCu,
      ← ENNReal.ofReal_add hv0 (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    push_cast at h
    exact h

/-- The growth of the constants in the last steps of the finite volume flow. -/
def Fc (d L : ℕ) (aK Cu c : ℝ) : ℝ :=
  max c (max (2 * (L : ℝ) ^ d * (1 + Cu) * c / (3 / 4)) (aK * (c + 2 * c ^ 2) / (3 / 4)))

theorem le_Fc {L : ℕ} (aK Cu c : ℝ) : c ≤ Fc d L aK Cu c := le_max_left _ _

/-- The constants `c_i = F^i(c_0)`. -/
def cc (d L : ℕ) (aK Cu c₀ : ℝ) (i : ℕ) : ℝ := (Fc d L aK Cu)^[i] c₀

theorem cc_mono {L : ℕ} (aK Cu c₀ : ℝ) : Monotone (cc d L aK Cu c₀) := by
  refine monotone_nat_of_le_succ fun i => ?_
  unfold cc
  rw [Function.iterate_succ_apply']
  exact le_Fc _ _ _

theorem cc_succ {L : ℕ} (aK Cu c₀ : ℝ) (i : ℕ) :
    cc d L aK Cu c₀ (i + 1) = Fc d L aK Cu (cc d L aK Cu c₀ i) := by
  unfold cc; rw [Function.iterate_succ_apply']

theorem cc_nonneg {L : ℕ} (aK Cu : ℝ) {c₀ : ℝ} (h : 0 ≤ c₀) (i : ℕ) : 0 ≤ cc d L aK Cu c₀ i :=
  h.trans (cc_mono aK Cu c₀ (Nat.zero_le i))

/-! ### The stable manifold for the renormalisation group flow -/

section Main

variable {L : ℕ} [NeZero L] {ℓ₀ A ε C₁ δK Kc Cw : ℝ} [Fact (0 < ℓ₀)] [Fact (0 < A)]

/-- The initial datum `w₀ = (b₀, K₀ = 0)`. -/
abbrev w0 (d L : ℕ) [NeZero L] (ℓ₀ A : ℝ) [Fact (0 < ℓ₀)] [Fact (0 < A)] (b₀ : ℂ) :
    WS d L ℓ₀ A 0 := (b₀, 0)

theorem norm_w0 (b₀ : ℂ) : ‖w0 d L ℓ₀ A b₀‖ = ‖b₀‖ := by
  simp [Prod.norm_def]

theorem δD_le (hd : 3 ≤ d) (hL : 2 ≤ L) (hδK : δK ≤ 1 / 2) : δD d L δK ≤ 1 / 2 := by
  refine max_le ?_ hδK
  have h1 : (2 : ℝ) ≤ (L : ℝ) ^ (d - 2) := by
    calc (2 : ℝ) ≤ L := by exact_mod_cast hL
      _ = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℝ) ^ (d - 2) := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ L))
          (by omega)
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

variable (H : Hyp d L A ℓ₀ ε C₁ δK Kc Cw) {R : ℝ}
  (hc : Admissible (βB d L ℓ₀ Kc Cw) (δD d L δK) (C₁ * cX d ℓ₀ ^ 2) (rad d ℓ₀ ε) (3 / 4) R)
include H hc

/-- The orbit on the stable manifold stays in the ball of radius `R ≤ r`. -/
theorem orbit_le_R (m : ℝ) {b₀ : ℂ} (hb : ‖b₀‖ ≤ rho (βB d L ℓ₀ Kc Cw) (δD d L δK) (3 / 4) R)
    (j : ℕ) :
    ‖(RGsys H m).orbit ((RGsys H m).stableMap (w0 d L ℓ₀ A b₀)) (w0 d L ℓ₀ A b₀) j‖ ≤ R := by
  have hS := RGsys_bounds H m
  have hw : ‖w0 d L ℓ₀ A b₀‖ ≤ rho (βB d L ℓ₀ Kc Cw) (δD d L δK) (3 / 4) R := by
    rw [norm_w0]; exact hb
  obtain ⟨v, ⟨hdec, hRv⟩, -⟩ := hS.existsUnique_stable hc hw
  rw [← hS.stableMap_unique hc hw hdec hRv]
  exact hRv j

theorem orbit_le_rad (m : ℝ) {b₀ : ℂ} (hb : ‖b₀‖ ≤ rho (βB d L ℓ₀ Kc Cw) (δD d L δK) (3 / 4) R)
    (j : ℕ) :
    ‖(RGsys H m).orbit ((RGsys H m).stableMap (w0 d L ℓ₀ A b₀)) (w0 d L ℓ₀ A b₀) j‖ ≤
      rad d ℓ₀ ε :=
  (orbit_le_R H hc m hb j).trans hc.R_le

/-- The constant `C_s = (1 + β/(1-θ)) (2θ/(θ-δ))` in the decay of the stable orbit. -/
def Cst (β δ : ℝ) : ℝ := (1 + β / (1 - 3 / 4)) * (2 * (3 / 4) / (3 / 4 - δ))

theorem orbit_decay (m : ℝ) {b₀ : ℂ} (hb : ‖b₀‖ ≤ rho (βB d L ℓ₀ Kc Cw) (δD d L δK) (3 / 4) R)
    (j : ℕ) :
    ‖((RGsys H m).orbit ((RGsys H m).stableMap (w0 d L ℓ₀ A b₀)) (w0 d L ℓ₀ A b₀) j).1‖ +
      ‖((RGsys H m).orbit ((RGsys H m).stableMap (w0 d L ℓ₀ A b₀)) (w0 d L ℓ₀ A b₀) j).2‖ ≤
      Cst (βB d L ℓ₀ Kc Cw) (δD d L δK) * (3 / 4) ^ j * ‖b₀‖ := by
  have hS := RGsys_bounds H m
  have hw : ‖w0 d L ℓ₀ A b₀‖ ≤ rho (βB d L ℓ₀ Kc Cw) (δD d L δK) (3 / 4) R := by
    rw [norm_w0]; exact hb
  have := hS.norm_orbit_stableMap_le hc hw j
  rwa [norm_w0] at this

/-- The constant `M_K = γ C_s² / (θ - δ)` in `‖K_j‖_j ≤ M_K |b₀|² θ^j`. -/
def Mk (β δ γ : ℝ) : ℝ := γ * Cst β δ ^ 2 / (3 / 4 - δ)

/-- **`K_j = O(b₀² θ^j)`**, by induction from `K₀ = 0` and the quadratic bound on `g_j`. -/
theorem orbit_K (m : ℝ) {b₀ : ℂ} (hb : ‖b₀‖ ≤ rho (βB d L ℓ₀ Kc Cw) (δD d L δK) (3 / 4) R)
    (j : ℕ) :
    ‖((RGsys H m).orbit ((RGsys H m).stableMap (w0 d L ℓ₀ A b₀)) (w0 d L ℓ₀ A b₀) j).2.2‖ ≤
      Mk (βB d L ℓ₀ Kc Cw) (δD d L δK) (C₁ * cX d ℓ₀ ^ 2) * ‖b₀‖ ^ 2 * (3 / 4) ^ j := by
  have hS := RGsys_bounds H m
  set o := (RGsys H m).orbit ((RGsys H m).stableMap (w0 d L ℓ₀ A b₀)) (w0 d L ℓ₀ A b₀) with ho
  set δ := δD d L δK
  set γ := C₁ * cX d ℓ₀ ^ 2
  set Cs := Cst (βB d L ℓ₀ Kc Cw) δ with hCs
  have hδθ : δ < 3 / 4 := hc.delta_lt
  have hδ0 : 0 ≤ δ := hc.delta_nonneg
  have hγ : 0 ≤ γ := hc.gamma_nonneg
  have hMk : 0 ≤ Mk (βB d L ℓ₀ Kc Cw) δ γ := by
    unfold Mk; have : 0 < 3 / 4 - δ := by linarith
    positivity
  have hMk' : δ * Mk (βB d L ℓ₀ Kc Cw) δ γ + γ * Cs ^ 2 = Mk (βB d L ℓ₀ Kc Cw) δ γ * (3 / 4) := by
    unfold Mk
    rw [← hCs, div_eq_mul_inv]
    have ht : (3 / 4 - δ) * (3 / 4 - δ)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
    linear_combination (-(γ * Cs ^ 2)) * ht
  induction j with
  | zero =>
    show ‖(0 : KFam d L 0 3 (ellj d (L : ℝ) ℓ₀ 0) A)‖ ≤ _
    rw [norm_zero]; positivity
  | succ j ih =>
    have hr := orbit_le_rad H hc m hb j
    rw [ho, RGsys_orbit_succ H m _ _ j hr, ← ho]
    show ‖FF H m j (o j)‖ ≤ _
    have e : FF H m j (o j) = DF H m j (o j).2.2 + ((RGsys H m).g j (o j)).2 := by
      show _ = DF H m j (o j).2.2 + (FF H m j (o j) - DF H m j (o j).2.2)
      abel
    have hg := hS.g_lipschitz j (o j) 0 hr (by rw [norm_zero]; exact (rad_pos H).le)
    rw [hS.g_zero, sub_zero, sub_zero, norm_zero, max_eq_left (norm_nonneg _)] at hg
    have hoj : ‖o j‖ ≤ Cs * (3 / 4) ^ j * ‖b₀‖ := by
      refine le_trans ?_ (orbit_decay H hc m hb j)
      rw [Prod.norm_def]
      exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
    have hDF : ‖DF H m j (o j).2.2‖ ≤ δ * ‖(o j).2.2‖ :=
      (DF H m j).le_of_opNorm_le ((norm_DF_le H m j).trans (le_max_right _ _)) (o j).2.2
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖((RGsys H m).g j (o j)).2‖ ≤ γ * ‖o j‖ * ‖o j‖ :=
      (norm_snd_le _).trans hg
    have hθj : (0 : ℝ) ≤ (3 / 4) ^ j := by positivity
    have hθ2 : ((3 : ℝ) / 4) ^ j * (3 / 4) ^ j ≤ (3 / 4) ^ j :=
      mul_le_of_le_one_left hθj (pow_le_one₀ (by norm_num) (by norm_num))
    have hoj0 : 0 ≤ ‖o j‖ := norm_nonneg _
    have hb0 : 0 ≤ ‖b₀‖ := norm_nonneg _
    have h3 : γ * ‖o j‖ * ‖o j‖ ≤ γ * Cs ^ 2 * ‖b₀‖ ^ 2 * (3 / 4) ^ j := by
      have h4 : ‖o j‖ * ‖o j‖ ≤ (Cs * (3 / 4) ^ j * ‖b₀‖) * (Cs * (3 / 4) ^ j * ‖b₀‖) :=
        mul_le_mul hoj hoj hoj0 (hoj0.trans hoj)
      calc γ * ‖o j‖ * ‖o j‖ = γ * (‖o j‖ * ‖o j‖) := by ring
        _ ≤ γ * ((Cs * (3 / 4) ^ j * ‖b₀‖) * (Cs * (3 / 4) ^ j * ‖b₀‖)) :=
          mul_le_mul_of_nonneg_left h4 hγ
        _ = γ * Cs ^ 2 * ‖b₀‖ ^ 2 * ((3 / 4) ^ j * (3 / 4) ^ j) := by ring
        _ ≤ γ * Cs ^ 2 * ‖b₀‖ ^ 2 * (3 / 4) ^ j :=
          mul_le_mul_of_nonneg_left hθ2 (by positivity)
    have h5 : δ * ‖(o j).2.2‖ ≤ δ * (Mk (βB d L ℓ₀ Kc Cw) δ γ * ‖b₀‖ ^ 2 * (3 / 4) ^ j) :=
      mul_le_mul_of_nonneg_left ih hδ0
    calc ‖DF H m j (o j).2.2‖ + ‖((RGsys H m).g j (o j)).2‖
        ≤ δ * ‖(o j).2.2‖ + γ * Cs ^ 2 * ‖b₀‖ ^ 2 * (3 / 4) ^ j := add_le_add hDF (h2.trans h3)
      _ ≤ (δ * Mk (βB d L ℓ₀ Kc Cw) δ γ + γ * Cs ^ 2) * ‖b₀‖ ^ 2 * (3 / 4) ^ j := by
          nlinarith
      _ = Mk (βB d L ℓ₀ Kc Cw) δ γ * ‖b₀‖ ^ 2 * (3 / 4) ^ (j + 1) := by
          rw [hMk', pow_succ]; ring

/-- The initial coupling constants `V_0^c(m², b₀)` on the stable manifold. -/
def Vc (m : ℝ) (b₀ : ℂ) : Vcoup :=
  VresL d L 0 ((RGsys H m).stableMap (w0 d L ℓ₀ A b₀), b₀)

omit hc in
theorem Vc_b (m : ℝ) (b₀ : ℂ) : (Vc H m b₀).b = b₀ := by
  simp [Vc]

/-- **Theorem `thm:flow`, the bounds `e:flowVK`** in the range `j + 3 ≤ N` where the torus flow
is the infinite volume flow: `‖V_j‖_j ≤ 4 c_V C_s θ^j |b₀|`, `‖K_j‖_j ≤ M_K θ^j |b₀|²`. -/
theorem flow_bounds_inf {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ}
    (hb : ‖b₀‖ ≤ rho (βB d L ℓ₀ Kc Cw) (δD d L δK) (3 / 4) R) {N j : ℕ} (hN : j + 3 ≤ N) :
    (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
        (flowN d L N msq (Vc H msq b₀) j).1).toReal ≤
      4 * cV d ℓ₀ * Cst (βB d L ℓ₀ Kc Cw) (δD d L δK) * (3 / 4) ^ j * ‖b₀‖ ∧
    (Knorm j (ellj d L ℓ₀ j) A (flowN d L N msq (Vc H msq b₀) j).2).toReal ≤
      Mk (βB d L ℓ₀ Kc Cw) (δD d L δK) (C₁ * cX d ℓ₀ ^ 2) * ‖b₀‖ ^ 2 * (3 / 4) ^ j := by
  obtain ⟨hV, hK⟩ := flowN_orbit H hmsq _ b₀ (orbit_le_rad H hc msq hb) j N hN
  rw [Vc, hV, hK]
  set o := (RGsys H msq).orbit ((RGsys H msq).stableMap (w0 d L ℓ₀ A b₀)) (w0 d L ℓ₀ A b₀)
  refine ⟨?_, (KFam.Knorm_le _ _).trans (orbit_K H hc msq hb j)⟩
  have h1 := Vnorm_VresL_le (d := d) (L := L) (N := N) (by have := H.hd; omega)
    (by omega : j ≤ N) H.hℓ₀ ((o j).1, (o j).2.1)
  refine (ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg (by norm_num)
    (cV_nonneg d ℓ₀)) (norm_nonneg _)) h1).trans ?_
  have h2 : ‖(((o j).1, (o j).2.1) : Vsp × ℂ)‖ ≤ ‖(o j).1‖ + ‖(o j).2‖ := by
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      ((norm_fst_le _).trans (le_add_of_nonneg_left (norm_nonneg _)))
  have h3 := orbit_decay H hc msq hb j
  have := cV_nonneg d ℓ₀
  calc 4 * cV d ℓ₀ * ‖(((o j).1, (o j).2.1) : Vsp × ℂ)‖ ≤
      4 * cV d ℓ₀ * (Cst (βB d L ℓ₀ Kc Cw) (δD d L δK) * (3 / 4) ^ j * ‖b₀‖) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
    _ = _ := by ring

omit hc in
theorem covAt_good (hgN : ∀ (M : ℕ) (msq : ℝ), 0 ≤ msq →
      GoodCov (d := d) (L := L) (N := M + 1) M ℓ₀ (CfrdN d L M msq))
    {N j : ℕ} (hj : j < N) {msq : ℝ} (hmsq : 0 ≤ msq) :
    GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j) := by
  rcases Nat.lt_or_ge (j + 1) N with h | h
  · rw [covAt_lt h]; exact H.good N j h msq hmsq
  · obtain rfl : N = j + 1 := by omega
    rw [covAt_last]; exact hgN j msq hmsq

/-- The constant `c_0 = 4 c_V C_s + M_K`. -/
def c0 (d L : ℕ) (ℓ₀ Kc Cw δK C₁ : ℝ) : ℝ :=
  4 * cV d ℓ₀ * Cst (βB d L ℓ₀ Kc Cw) (δD d L δK) + Mk (βB d L ℓ₀ Kc Cw) (δD d L δK) (C₁ * cX d ℓ₀ ^ 2)

theorem Cst_nonneg : 0 ≤ Cst (βB d L ℓ₀ Kc Cw) (δD d L δK) := by
  unfold Cst
  have := hc.beta_nonneg; have := hc.delta_lt
  have h : 0 < 3 / 4 - δD d L δK := by linarith
  positivity

theorem Mk_nonneg : 0 ≤ Mk (βB d L ℓ₀ Kc Cw) (δD d L δK) (C₁ * cX d ℓ₀ ^ 2) := by
  unfold Mk
  have := hc.gamma_nonneg; have := hc.delta_lt
  have h : 0 < 3 / 4 - δD d L δK := by linarith
  positivity

theorem c0_nonneg : 0 ≤ c0 d L ℓ₀ Kc Cw δK C₁ := by
  unfold c0
  have := Cst_nonneg H hc; have := Mk_nonneg H hc; have := cV_nonneg d ℓ₀
  positivity

/-- **Corollary `cor:flow-finvol`**: the bounds `e:flowVK` for the finite volume flow for all
`j ≤ N` (with the constant `c_{j+3-N}`), and `K_j ∈ 𝒦_j` for `j < N`. -/
theorem flow_bounds_fin {ε' aK Cu : ℝ} (haK : 0 ≤ aK) (hCu : 0 ≤ Cu)
    (hstep : ∀ (N j : ℕ), j < N →
      ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
      ∀ (V : Vcoup) (K : Act d L N), InK j K →
        (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal +
            (Knorm j (ellj d L ℓ₀ j) A K).toReal ≤ ε' →
        (Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (Knext j C V K)).toReal ≤
            aK * ((Knorm j (ellj d L ℓ₀ j) A K).toReal +
              (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal ^ 2 +
              (Knorm j (ellj d L ℓ₀ j) A K).toReal ^ 2) ∧
        (Vnorm (d := d) (L := L) (N := N) (j + 1) (ellj d L ℓ₀ (j + 1)) (uVnext j C V K).2).toReal ≤
            2 * (L : ℝ) ^ d * ((Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal +
              Cu * (Knorm j (ellj d L ℓ₀ j) A K).toReal) ∧
        ‖(uVnext j C V K).1‖ * (L : ℝ) ^ (j * d) ≤
            (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V).toReal +
              Cu * (Knorm j (ellj d L ℓ₀ j) A K).toReal)
    (hgN : ∀ (M : ℕ) (msq : ℝ), 0 ≤ msq →
      GoodCov (d := d) (L := L) (N := M + 1) M ℓ₀ (CfrdN d L M msq))
    {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ}
    (hb : ‖b₀‖ ≤ rho (βB d L ℓ₀ Kc Cw) (δD d L δK) (3 / 4) R) (hb1 : ‖b₀‖ ≤ 1)
    (hbε : 2 * cc d L aK Cu (c0 d L ℓ₀ Kc Cw δK C₁) 3 * ‖b₀‖ ≤ ε') (N : ℕ) :
    ∀ j, j ≤ N →
      (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
          (flowN d L N msq (Vc H msq b₀) j).1).toReal ≤
        cc d L aK Cu (c0 d L ℓ₀ Kc Cw δK C₁) (j + 3 - N) * ‖b₀‖ * (3 / 4) ^ j ∧
      (Knorm j (ellj d L ℓ₀ j) A (flowN d L N msq (Vc H msq b₀) j).2).toReal ≤
        cc d L aK Cu (c0 d L ℓ₀ Kc Cw δK C₁) (j + 3 - N) * ‖b₀‖ ^ 2 * (3 / 4) ^ j ∧
      (j < N → InK j (flowN d L N msq (Vc H msq b₀) j).2) := by
  set c₀ := c0 d L ℓ₀ Kc Cw δK C₁ with hc₀
  have hc₀0 : 0 ≤ c₀ := c0_nonneg H hc
  have hCs := Cst_nonneg H hc
  have hMk := Mk_nonneg H hc
  have hcV := cV_nonneg d ℓ₀
  have hb0 : 0 ≤ ‖b₀‖ := norm_nonneg _
  intro j
  induction j with
  | zero =>
    intro _
    rcases Nat.lt_or_ge N 3 with hN | hN
    · -- small tori: `V_0 = V_0^c`, `K_0 = 0`
      refine ⟨?_, ?_, fun _ => InK.zero 0⟩
      · rw [flowN_zero, Vc]
        have h1 := Vnorm_VresL_le (d := d) (L := L) (N := N) (by have := H.hd; omega)
          (Nat.zero_le N) H.hℓ₀ ((RGsys H msq).stableMap (w0 d L ℓ₀ A b₀), b₀)
        refine (ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg (by norm_num) hcV)
          (norm_nonneg _)) h1).trans ?_
        have h3 := orbit_decay H hc msq hb 0
        simp only [System.orbit, pow_zero, mul_one] at h3
        have h2 : ‖(((RGsys H msq).stableMap (w0 d L ℓ₀ A b₀), b₀) : Vsp × ℂ)‖ ≤
            ‖(RGsys H msq).stableMap (w0 d L ℓ₀ A b₀)‖ + ‖w0 d L ℓ₀ A b₀‖ := by
          rw [Prod.norm_def, norm_w0]
          exact max_le (le_add_of_nonneg_right (norm_nonneg _))
            (le_add_of_nonneg_left (norm_nonneg _))
        have h4 : c₀ ≤ cc d L aK Cu c₀ (0 + 3 - N) := cc_mono aK Cu c₀ (Nat.zero_le _)
        calc 4 * cV d ℓ₀ * ‖(((RGsys H msq).stableMap (w0 d L ℓ₀ A b₀), b₀) : Vsp × ℂ)‖
            ≤ 4 * cV d ℓ₀ * (Cst (βB d L ℓ₀ Kc Cw) (δD d L δK) * ‖b₀‖) :=
              mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
          _ ≤ c₀ * ‖b₀‖ := by
              rw [hc₀, c0]; nlinarith
          _ ≤ cc d L aK Cu c₀ (0 + 3 - N) * ‖b₀‖ * (3 / 4) ^ 0 := by
              rw [pow_zero, mul_one]; exact mul_le_mul_of_nonneg_right h4 hb0
      · rw [flowN_zero, Knorm_zero, ENNReal.toReal_zero]
        have := cc_nonneg (d := d) (L := L) aK Cu hc₀0 (0 + 3 - N)
        positivity
    · obtain ⟨hV, hK⟩ := flow_bounds_inf H hc hmsq hb (by omega : 0 + 3 ≤ N)
      have h0 : 0 + 3 - N = 0 := by omega
      rw [h0]
      refine ⟨hV.trans ?_, hK.trans ?_, fun _ => ?_⟩
      · simp only [cc, Function.iterate_zero, id, hc₀, c0]; nlinarith
      · simp only [cc, Function.iterate_zero, id, hc₀, c0]
        nlinarith [mul_nonneg (mul_nonneg hcV hCs) (pow_nonneg hb0 2)]
      · obtain ⟨-, hK'⟩ := flowN_orbit H hmsq _ b₀ (orbit_le_rad H hc msq hb) 0 N hN
        rw [Vc, hK']
        exact KFam.inK _ _
  | succ j ih =>
    intro hjN
    rcases Nat.lt_or_ge (j + 1 + 3) (N + 1) with hN | hN
    · -- the infinite volume range
      obtain ⟨hV, hK⟩ := flow_bounds_inf H hc hmsq hb (by omega : j + 1 + 3 ≤ N)
      have h0 : j + 1 + 3 - N = 0 := by omega
      rw [h0]
      refine ⟨hV.trans ?_, hK.trans ?_, fun _ => ?_⟩
      · simp only [cc, Function.iterate_zero, id, hc₀, c0]
        have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (j + 1)
        nlinarith [mul_nonneg hMk (mul_nonneg hb0 this)]
      · simp only [cc, Function.iterate_zero, id, hc₀, c0]
        have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (j + 1)
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hcV hCs) (pow_nonneg hb0 2)) this]
      · obtain ⟨-, hK'⟩ := flowN_orbit H hmsq _ b₀ (orbit_le_rad H hc msq hb) (j + 1) N
          (by omega)
        rw [Vc, hK']
        exact KFam.inK _ _
    · -- the last steps
      obtain ⟨ihV, ihK, ihI⟩ := ih (by omega)
      have hjN' : j < N := by omega
      have hi : j + 1 + 3 - N = (j + 3 - N) + 1 := by omega
      have hc3 : cc d L aK Cu c₀ (j + 3 - N) ≤ cc d L aK Cu c₀ 3 := cc_mono aK Cu c₀ (by omega)
      have hc0 : 0 ≤ cc d L aK Cu c₀ (j + 3 - N) := cc_nonneg aK Cu hc₀0 _
      have hS := hstep N j hjN' _ (covAt_good H hgN hjN' hmsq) (flowN d L N msq (Vc H msq b₀) j).1
        (flowN d L N msq (Vc H msq b₀) j).2 (ihI hjN')
      have hv0 : 0 ≤ (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
        (flowN d L N msq (Vc H msq b₀) j).1).toReal := ENNReal.toReal_nonneg
      have hk0 : 0 ≤ (Knorm j (ellj d L ℓ₀ j) A (flowN d L N msq (Vc H msq b₀) j).2).toReal :=
        ENNReal.toReal_nonneg
      rw [hi, cc_succ]
      simp only [flowN_succ]
      rw [Knorm_restr]
      refine ⟨?_, ?_, fun hj1 => ?_⟩
      rotate_right
      · exact (restr_mem (by omega) (InK_Knext H.hd1 H.hL8 hj1
          (covAt_good H hgN hjN' hmsq) _ (ihI hjN'))).1
      all_goals
        generalize hcdef : cc d L aK Cu c₀ (j + 3 - N) = c at ihV ihK hc3 hc0 ⊢
        generalize hv : (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j)
          (flowN d L N msq (Vc H msq b₀) j).1).toReal = v at ihV hS hv0
        generalize hk : (Knorm j (ellj d L ℓ₀ j) A
          (flowN d L N msq (Vc H msq b₀) j).2).toReal = k at ihK hS hk0
      all_goals
        have hθ0 : (0 : ℝ) ≤ (3 / 4) ^ j := by positivity
        have hθ1 : ((3 : ℝ) / 4) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have hb2 : ‖b₀‖ ^ 2 ≤ ‖b₀‖ := by nlinarith
        have hkθ : k ≤ c * ‖b₀‖ * (3 / 4) ^ j := by
          refine ihK.trans ?_
          have h1 := mul_le_mul_of_nonneg_left hb2 hc0
          have h2 := mul_le_mul_of_nonneg_right h1 hθ0
          linarith
        have hv' : v ≤ c * ‖b₀‖ := by
          have := mul_le_mul_of_nonneg_left hθ1 (mul_nonneg hc0 hb0)
          linarith
        have hk' : k ≤ c * ‖b₀‖ := by
          have := mul_le_mul_of_nonneg_left hθ1 (mul_nonneg hc0 hb0)
          linarith
        have hsmall : v + k ≤ ε' := by
          have := mul_le_mul_of_nonneg_right hc3 hb0
          linarith
        have hθθ : ((3 : ℝ) / 4) ^ j * (3 / 4) ^ j ≤ (3 / 4) ^ j := mul_le_of_le_one_left hθ0 hθ1
        obtain ⟨hK1, hV1, -⟩ := hS hsmall
        clear hS
      · refine hV1.trans ?_
        have hFc : 2 * (L : ℝ) ^ d * (1 + Cu) * c / (3 / 4) ≤ Fc d L aK Cu c :=
          (le_max_left _ _).trans (le_max_right _ _)
        have hL0 : (0 : ℝ) ≤ 2 * (L : ℝ) ^ d := by positivity
        have e1 : v + Cu * k ≤ (1 + Cu) * c * ‖b₀‖ * (3 / 4) ^ j := by
          have := mul_le_mul_of_nonneg_left hkθ hCu
          linarith
        have hbθ : 0 ≤ ‖b₀‖ * (3 / 4) ^ (j + 1) := by positivity
        calc 2 * (L : ℝ) ^ d * (v + Cu * k) ≤ 2 * (L : ℝ) ^ d * ((1 + Cu) * c * ‖b₀‖ * (3 / 4) ^ j) :=
              mul_le_mul_of_nonneg_left e1 hL0
          _ = 2 * (L : ℝ) ^ d * (1 + Cu) * c / (3 / 4) * (‖b₀‖ * (3 / 4) ^ (j + 1)) := by
              rw [pow_succ]; field_simp
          _ ≤ Fc d L aK Cu c * (‖b₀‖ * (3 / 4) ^ (j + 1)) := mul_le_mul_of_nonneg_right hFc hbθ
          _ = Fc d L aK Cu c * ‖b₀‖ * (3 / 4) ^ (j + 1) := by ring
      · refine hK1.trans ?_
        have hFc : aK * (c + 2 * c ^ 2) / (3 / 4) ≤ Fc d L aK Cu c :=
          (le_max_right _ _).trans (le_max_right _ _)
        have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
        have hB2 : 0 ≤ ‖b₀‖ ^ 2 := sq_nonneg _
        have hv2 : v ^ 2 ≤ c ^ 2 * ‖b₀‖ ^ 2 * (3 / 4) ^ j := by
          have h1 : v ^ 2 ≤ (c * ‖b₀‖ * (3 / 4) ^ j) ^ 2 := pow_le_pow_left₀ hv0 ihV 2
          have h2 : (c * ‖b₀‖ * (3 / 4) ^ j) ^ 2 = c ^ 2 * ‖b₀‖ ^ 2 * ((3 / 4) ^ j * (3 / 4) ^ j) := by
            ring
          have h3 := mul_le_mul_of_nonneg_left hθθ (mul_nonneg hc2 hB2)
          linarith
        have hk2 : k ^ 2 ≤ c ^ 2 * ‖b₀‖ ^ 2 * (3 / 4) ^ j := by
          have h1 : k ^ 2 ≤ (c * ‖b₀‖ ^ 2 * (3 / 4) ^ j) ^ 2 := pow_le_pow_left₀ hk0 ihK 2
          have h2 : (c * ‖b₀‖ ^ 2 * (3 / 4) ^ j) ^ 2 =
              c ^ 2 * (‖b₀‖ ^ 2 * ‖b₀‖ ^ 2) * ((3 / 4) ^ j * (3 / 4) ^ j) := by ring
          have hb4 : ‖b₀‖ ^ 2 * ‖b₀‖ ^ 2 ≤ ‖b₀‖ ^ 2 :=
            mul_le_of_le_one_left hB2 (pow_le_one₀ hb0 hb1)
          have h3 : c ^ 2 * (‖b₀‖ ^ 2 * ‖b₀‖ ^ 2) * ((3 / 4) ^ j * (3 / 4) ^ j) ≤
              c ^ 2 * ‖b₀‖ ^ 2 * (3 / 4) ^ j :=
            mul_le_mul (mul_le_mul_of_nonneg_left hb4 hc2) hθθ (by positivity) (by positivity)
          linarith
        have e1 : k + v ^ 2 + k ^ 2 ≤ (c + 2 * c ^ 2) * ‖b₀‖ ^ 2 * (3 / 4) ^ j :=
          calc k + v ^ 2 + k ^ 2 ≤ c * ‖b₀‖ ^ 2 * (3 / 4) ^ j + c ^ 2 * ‖b₀‖ ^ 2 * (3 / 4) ^ j +
                c ^ 2 * ‖b₀‖ ^ 2 * (3 / 4) ^ j := add_le_add (add_le_add ihK hv2) hk2
            _ = (c + 2 * c ^ 2) * ‖b₀‖ ^ 2 * (3 / 4) ^ j := by ring
        have hbθ : 0 ≤ ‖b₀‖ ^ 2 * (3 / 4) ^ (j + 1) := by positivity
        calc aK * (k + v ^ 2 + k ^ 2) ≤ aK * ((c + 2 * c ^ 2) * ‖b₀‖ ^ 2 * (3 / 4) ^ j) :=
              mul_le_mul_of_nonneg_left e1 haK
          _ = aK * (c + 2 * c ^ 2) / (3 / 4) * (‖b₀‖ ^ 2 * (3 / 4) ^ (j + 1)) := by
              rw [pow_succ ((3 : ℝ) / 4) j]; field_simp
          _ ≤ Fc d L aK Cu c * (‖b₀‖ ^ 2 * (3 / 4) ^ (j + 1)) := mul_le_mul_of_nonneg_right hFc hbθ
          _ = Fc d L aK Cu c * ‖b₀‖ ^ 2 * (3 / 4) ^ (j + 1) := by ring

omit hc in
theorem Vc_z (m : ℝ) (b₀ : ℂ) : (Vc H m b₀).z = ((RGsys H m).stableMap (w0 d L ℓ₀ A b₀)).1 := rfl

omit hc in
theorem Vc_y (m : ℝ) (b₀ : ℂ) : (Vc H m b₀).y = ((RGsys H m).stableMap (w0 d L ℓ₀ A b₀)).2.1 :=
  rfl

omit hc in
theorem Vc_a (m : ℝ) (b₀ : ℂ) : (Vc H m b₀).a = ((RGsys H m).stableMap (w0 d L ℓ₀ A b₀)).2.2 := by
  simp [Vc]

end Main

theorem theta_pow_eq {L : ℕ} (hL : 2 ≤ L) (j : ℕ) :
    ((3 : ℝ) / 4) ^ j = (L : ℝ) ^ (-(Real.logb L (4 / 3) * j)) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hL0 : (0 : ℝ) < L := by linarith
  rw [Real.rpow_neg hL0.le, Real.rpow_mul hL0.le,
    Real.rpow_logb hL0 hL1.ne' (by norm_num), Real.rpow_natCast, ← inv_pow, inv_div]

end

end Flow
