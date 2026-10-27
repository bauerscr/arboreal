import Step2.Coup.WickAsm

/-!
# The `g`-component of the current step (`h02uv-outline.tex`, `prop:C4b`(b), (c))

With `e_z, e_y, e_ν, e_g` the unit couplings, `C = C'_{j+1}`, `C⁽¹⁾ = ∑_x C(x, 0)`:

* `betaQ_self_g_eq`: `β^q_{j,j}(u, v)_g = mu4(F_C(V_u(B_+), V_v(Λ))) / (2 |B_+|)`;
* `betaQ_g_nu`: `β^q_{j,j}(e_g, e_ν)_g + β^q_{j,j}(e_ν, e_g)_g = 4 C⁽¹⁾`;
* `betaQ_g_z`, `betaQ_g_y`: the gradient cross terms vanish;
* `qjj_g`: `q_{j,j}(u)_g = u_g² q_{j,j}(e_g)_g + 4 C⁽¹⁾ u_g u_ν`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-! ### The unit couplings -/

/-- The unit couplings `e_z, e_y, e_ν, e_g`. -/
abbrev eC (a : Fin 4) : Fin 4 → ℂ := Pi.single a 1

theorem VcoupL_eg (Y : Finset (Lam d L N)) :
    VcoupL Y (eC 3) = ∑ i, mono4sSet i i Y := by
  show unif 0 (coupC (Coup.ofVec (eC 3))) (coupE (Coup.ofVec (eC 3))) Y = _
  have hc : ∀ M : Mono d, coupC (Coup.ofVec (eC 3)) M = 0 := by
    intro M; cases M <;> simp [coupC, Coup.ofVec]
  rw [unif]
  simp only [hc, zero_smul, sum_const_zero, add_zero, zero_add]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_eq_single i]
  · simp [coupE, Coup.ofVec]
  · intro k _ hk; simp [coupE, Ne.symm hk]
  · simp

theorem VcoupL_enu (Y : Finset (Lam d L N)) :
    VcoupL Y (eC 2) = monoSet (Mono.c : Mono d) Y := by
  show unif 0 (coupC (Coup.ofVec (eC 2))) (coupE (Coup.ofVec (eC 2))) Y = _
  have he : ∀ i k : Fin d, coupE (Coup.ofVec (eC 2)) i k = 0 := by
    intro i k; simp [coupE, Coup.ofVec]
  simp only [unif, he, zero_smul, sum_const_zero, add_zero, zero_add]
  rw [sum_eq_single (Mono.c : Mono d)]
  · simp [coupC, Coup.ofVec]
  · intro M _ hM; cases M <;> simp_all [coupC, Coup.ofVec]
  · simp

theorem VcoupL_ez (Y : Finset (Lam d L N)) :
    VcoupL Y (eC 0) = ∑ i, monoSet (Mono.m2 i i : Mono d) Y := by
  show unif 0 (coupC (Coup.ofVec (eC 0))) (coupE (Coup.ofVec (eC 0))) Y = _
  have he : ∀ i k : Fin d, coupE (Coup.ofVec (eC 0)) i k = 0 := by
    intro i k; simp [coupE, Coup.ofVec]
  simp only [unif, he, zero_smul, sum_const_zero, add_zero, zero_add]
  rw [sum_mono]
  simp only [coupC, Coup.ofVec, eC]
  simp [Pi.single_apply, ite_smul]

theorem VcoupL_ey (Y : Finset (Lam d L N)) :
    VcoupL Y (eC 1) = ∑ i, (-(1 / 2 : ℂ)) •
      (monoSet (Mono.a2 s(i, i) : Mono d) Y + monoSet (Mono.b2 s(i, i)) Y) := by
  show unif 0 (coupC (Coup.ofVec (eC 1))) (coupE (Coup.ofVec (eC 1))) Y = _
  have he : ∀ i k : Fin d, coupE (Coup.ofVec (eC 1)) i k = 0 := by
    intro i k; simp [coupE, Coup.ofVec]
  simp only [unif, he, zero_smul, sum_const_zero, add_zero, zero_add]
  rw [sum_mono]
  simp only [coupC, Coup.ofVec, eC]
  simp only [ite_smul, zero_smul, sum_const_zero, add_zero, zero_add, sum_sym2_diag]
  simp [Pi.single_apply, smul_add, sum_add_distrib, neg_div]

/-! ### The `g`-component of `β^q_{j,j}` -/

theorem FC_sum_left {ι : Type*} (C : Matrix (Lam d L N) (Lam d L N) ℂ) (s : Finset ι)
    (A : ι → Alg d L N) (B : Alg d L N) : FC C (∑ i ∈ s, A i) B = ∑ i ∈ s, FC C (A i) B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    have := FC_const_left C 0 B
    rwa [zero_smul] at this
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, FC_add_left, ih]

theorem sum_VcoupL_blocks {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (v : Fin 4 → ℂ) :
    ∑ b' ∈ blocks j X, VcoupL (blockSet (L := L) (N := N) j b') v = VcoupL X v := by
  show ∑ b' ∈ blocks j X, Vcoup (Coup.ofVec v) (blockSet j b') = Vcoup (Coup.ofVec v) X
  simp only [Vcoup]
  rw [unif_sum _ _ _ _ _ (pairwiseDisjoint_blockSet' j _), mul_zero, biUnion_blocks hX]

namespace FlowSeq

variable (D : FlowSeq d L N)

/-- **`β^q_{j,j}(u, v)_g = mu4(F_C(V_u(B_+), V_v(Λ))) / (2 |B_+|)`.** -/
theorem betaQ_self_g_eq (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) (u v : Fin 4 → ℂ) :
    D.betaQ j j b i₀ u v 3 = mu4 (base (Bp (L := L) (N := N) j b)) i₀ i₀
      (FC (D.C j) (VcoupL (Bp (L := L) (N := N) j b) u) (VcoupL univ v)) /
        (2 * (Bp (L := L) (N := N) j b).card) := by
  have hsm := isSmall_blockSet_of_mem hb
  have hP := patch_of_small hL hj hsm
  have hBp : IsSmall (j + 1) (Bp (L := L) (N := N) j b) := isSmall_clo hsm
  have hB0 : ((blockSet (L := L) (N := N) j b).card : ℂ) ≠ 0 := by
    exact_mod_cast hsm.2.1.1.card_pos.ne'
  have hH : ((∑ b' ∈ blocks j (Bp (L := L) (N := N) j b),
      SrcF j (D.C j) LinearMap.id (VfamL j u) (VfamL j v) b' : EvR (Lam d L N)) : Alg d L N) =
      (1 / 2 : ℂ) • FC (D.C j) (VcoupL (Bp (L := L) (N := N) j b) u) (VcoupL univ v) := by
    simp only [SrcF, LinearMap.id_apply, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul,
      coe_FCE]
    have h1 : ∑ b'' ∈ blockIdx (L := L) (N := N) j,
        ((VfamL (d := d) (L := L) (N := N) j v b'' : EvR (Lam d L N)) : Alg d L N) =
        VcoupL univ v := sum_VcoupL_blocks (L := L) (N := N) (isPolymer_univ j) v
    rw [h1, ← smul_sum, ← FC_sum_left]
    show (1 / 2 : ℂ) • FC (D.C j) (∑ b' ∈ blocks j (Bp (L := L) (N := N) j b),
      VcoupL (blockSet (L := L) (N := N) j b') u) _ = _
    congr 2
    exact sum_VcoupL_blocks (IsPolymer.of_succ hBp.1) u
  unfold betaQ
  rw [if_pos rfl]
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply]
  rw [cvec4_g]
  simp only [LS0L, LinearMap.mk₂_apply, LS0, AlgHom.toLinearMap_apply, Subalgebra.coe_val,
    coe_Loc2E]
  rw [hH, Loc2sXY, mu4_add, mu4_LocXY, zero_add, Loc4sXY, mu4_sum]
  simp only [mu4_sum, mu4_smul, mu4_mono4Set hP]
  rw [sum_eq_single i₀ (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
  rw [sum_eq_single i₀ (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
  simp only [if_true, one_mul]
  field_simp

/-- **The `gν` coefficient**: `β^q_{j,j}(e_g, e_ν)_g + β^q_{j,j}(e_ν, e_g)_g = 4 C⁽¹⁾`. -/
theorem betaQ_g_nu (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) {r : ℕ} (H : CovH (D.C j) r)
    (hX : ∀ x ∈ Bp (L := L) (N := N) j b,
      2 * (supNorm (x - base (Bp (L := L) (N := N) j b)) + r + 4) < L ^ N) :
    D.betaQ j j b i₀ (eC 3) (eC 2) 3 + D.betaQ j j b i₀ (eC 2) (eC 3) 3 =
      4 * ∑ x, (D.C j) x 0 := by
  have hsm := isSmall_blockSet_of_mem hb
  have hBp : IsSmall (j + 1) (Bp (L := L) (N := N) j b) := isSmall_clo hsm
  have hc : ((Bp (L := L) (N := N) j b).card : ℂ) ≠ 0 := by
    exact_mod_cast hBp.2.1.1.card_pos.ne'
  have ev : ∀ (Y : Finset (Lam d L N)) (v : Fin 4 → ℂ), inv' (VcoupL Y v) = VcoupL Y v :=
    fun Y v => mem_Ev.1 (unif_mem_Ev _ _ _ _)
  rw [D.betaQ_self_g_eq hL hj hb, D.betaQ_self_g_eq hL hj hb,
    FC_comm _ (ev _ _) (ev _ _),
    mu4_FC_eq_Xc _ (ev _ _) (degLe_VcoupL_quad _ (by simp)) (degLe_VcoupL _ _),
    mu4_FC_eq_Xc _ (ev _ _) (degLe_VcoupL_quad _ (by simp)) (degLe_VcoupL _ _),
    VcoupL_enu, VcoupL_enu, VcoupL_eg, VcoupL_eg]
  simp only [← XcL_apply, map_sum, mu4_sum]
  simp only [XcL_apply, H.mu4_mass_univ_X (b := base (Bp (L := L) (N := N) j b))
      (X := Bp (L := L) (N := N) j b) (fun x hx => by have := hX x hx; omega),
    H.mu4_mass_X_univ (b := base (Bp (L := L) (N := N) j b))
      (X := Bp (L := L) (N := N) j b) (fun x hx => by have := hX x hx; omega)]
  rw [sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp)]
  simp only [if_true]
  field_simp
  ring

/-- **The `g z` cross term vanishes.** -/
theorem betaQ_g_z (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) {r : ℕ} (H : CovH (D.C j) r)
    (hX : ∀ x ∈ Bp (L := L) (N := N) j b,
      2 * (supNorm (x - base (Bp (L := L) (N := N) j b)) + r + 4) < L ^ N) :
    D.betaQ j j b i₀ (eC 3) (eC 0) 3 + D.betaQ j j b i₀ (eC 0) (eC 3) 3 = 0 := by
  have ev : ∀ (Y : Finset (Lam d L N)) (v : Fin 4 → ℂ), inv' (VcoupL Y v) = VcoupL Y v :=
    fun Y v => mem_Ev.1 (unif_mem_Ev _ _ _ _)
  rw [D.betaQ_self_g_eq hL hj hb, D.betaQ_self_g_eq hL hj hb,
    FC_comm _ (ev _ _) (ev _ _),
    mu4_FC_eq_Xc _ (ev _ _) (degLe_VcoupL_quad _ (by simp)) (degLe_VcoupL _ _),
    mu4_FC_eq_Xc _ (ev _ _) (degLe_VcoupL_quad _ (by simp)) (degLe_VcoupL _ _),
    VcoupL_ez, VcoupL_ez, VcoupL_eg, VcoupL_eg]
  simp only [← XcL_apply, map_sum, LinearMap.sum_apply, mu4_sum]
  simp only [XcL_apply, H.mu4_m2_univ_X hX, H.mu4_m2_X_univ hX, sum_const_zero]
  simp

/-- **The `g y` cross term vanishes.** -/
theorem betaQ_g_y (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) {r : ℕ} (H : CovH (D.C j) r)
    (hX : ∀ x ∈ Bp (L := L) (N := N) j b,
      2 * (supNorm (x - base (Bp (L := L) (N := N) j b)) + r + 4) < L ^ N) :
    D.betaQ j j b i₀ (eC 3) (eC 1) 3 + D.betaQ j j b i₀ (eC 1) (eC 3) 3 = 0 := by
  have ev : ∀ (Y : Finset (Lam d L N)) (v : Fin 4 → ℂ), inv' (VcoupL Y v) = VcoupL Y v :=
    fun Y v => mem_Ev.1 (unif_mem_Ev _ _ _ _)
  rw [D.betaQ_self_g_eq hL hj hb, D.betaQ_self_g_eq hL hj hb,
    FC_comm _ (ev _ _) (ev _ _),
    mu4_FC_eq_Xc _ (ev _ _) (degLe_VcoupL_quad _ (by simp)) (degLe_VcoupL _ _),
    mu4_FC_eq_Xc _ (ev _ _) (degLe_VcoupL_quad _ (by simp)) (degLe_VcoupL _ _),
    VcoupL_ey, VcoupL_ey, VcoupL_eg, VcoupL_eg]
  simp only [← XcL_apply, map_sum, map_smul, map_add, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.add_apply, mu4_sum, mu4_smul, mu4_add]
  simp only [XcL_apply, H.mu4_a2_univ_X hX, H.mu4_a2_X_univ hX, H.mu4_b2_univ_X hX,
    H.mu4_b2_X_univ hX, add_zero, mul_zero, sum_const_zero]
  simp

/-- **`prop:C4b`(b) at the current step**: `q_{j,j}(u)_g = u_g² q_{j,j}(e_g)_g + 4 C⁽¹⁾ u_g u_ν`. -/
theorem qjj_g (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) {r : ℕ} (H : CovH (D.C j) r)
    (hX : ∀ x ∈ Bp (L := L) (N := N) j b,
      2 * (supNorm (x - base (Bp (L := L) (N := N) j b)) + r + 4) < L ^ N) (u : Fin 4 → ℂ) :
    D.betaQ j j b i₀ u u 3 = u 3 ^ 2 * D.betaQ j j b i₀ (eC 3) (eC 3) 3 +
      4 * (∑ x, (D.C j) x 0) * u 3 * u 2 := by
  rw [D.betaQ_self_g j b i₀ u]
  have huq : u - u 3 • Pi.single 3 1 = u 0 • eC 0 + u 1 • eC 1 + u 2 • eC 2 := by
    funext a; fin_cases a <;> simp [eC]
  rw [huq]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  have hz := D.betaQ_g_z hL hj hb i₀ H hX
  have hy := D.betaQ_g_y hL hj hb i₀ H hX
  have hn := D.betaQ_g_nu hL hj hb i₀ H hX
  show _ = u 3 ^ 2 * D.betaQ j j b i₀ (Pi.single 3 1) (Pi.single 3 1) 3 + _
  linear_combination (u 3 * u 0) * hz + (u 3 * u 1) * hy + (u 3 * u 2) * hn

end FlowSeq

namespace FlowSeq

variable (D : FlowSeq d L N)

/-- **`prop:C4b`(b), exact**: the `g`-component of `κ_S^lin` at step `j` is
`∑_{k<j} g_k² b_{j,k} + g_j² q_{j,j}(e_g)_g + 4 C⁽¹⁾ g_j ν'_j`, with `ν'_j = ν_j + 2d g_j δ`,
`b_{j,k} = β_{j,k}(e_g, e_g)_g` and `C⁽¹⁾ = ∑_x C'_{j+1}(x, 0)`. -/
theorem kappaS_g (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hjN : j + 1 < N)
    {ℓ : ℝ} (hC : ∀ i, GoodCov2 i ℓ (D.C i)) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) {r : ℕ} (H : CovH (D.C j) r)
    (hX : ∀ x ∈ Bp (L := L) (N := N) j b,
      2 * (supNorm (x - base (Bp (L := L) (N := N) j b)) + r + 4) < L ^ N)
    {c₀ δ : ℂ} (hc₀ : ∀ x, D.C j x x = c₀) (hδ : ∀ x e, D.C j (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, D.C j x (x + dirVec e) = c₀ + δ) :
    cvec4 (blockSet (L := L) (N := N) j b) i₀
      (LS j (D.C j) (D.Vin j) (fun b' => sigE (D.s j) (D.Wlin j b')) b : Alg d L N) 3 =
      ∑ k ∈ range j, (D.κ k).g ^ 2 * D.beta j k b i₀ (eC 3) (eC 3) 3 +
        (D.κ j).g ^ 2 * D.betaQ j j b i₀ (eC 3) (eC 3) 3 +
        4 * (∑ x, (D.C j) x 0) * (D.κ j).g * ((D.κ j).nu + 2 * d * (D.κ j).g * δ) := by
  have h3 : cvec4 (blockSet (L := L) (N := N) j b) i₀
      (LS j (D.C j) (D.Vin j) (fun b' => sigE (D.s j) (D.Wlin j b')) b : Alg d L N) 3 =
      ∑ k ∈ range (j + 1), D.beta j k b i₀ (D.κ k).toVec (D.κ k).toVec 3 := by
    rw [D.kappaS_quad j b i₀]; exact Finset.sum_apply _ _ _
  have hpast : ∑ k ∈ range j, D.beta j k b i₀ (D.κ k).toVec (D.κ k).toVec 3 =
      ∑ k ∈ range j, (D.κ k).g ^ 2 * D.beta j k b i₀ (eC 3) (eC 3) 3 :=
    sum_congr rfl fun k hk => by
      rw [D.beta_past_g hd hL (mem_range.1 hk) hjN (fun i _ => hC i) hb i₀]; rfl
  have hs3 : shiftL d c₀ δ (D.κ j).toVec 3 = (D.κ j).g := by simp [shiftL, Coup.toVec]
  have hs2 : shiftL d c₀ δ (D.κ j).toVec 2 = (D.κ j).nu + 2 * d * (D.κ j).g * δ := by
    simp [shiftL, Coup.toVec]
  rw [h3, sum_range_succ, hpast, D.beta_eq_betaQ hc₀ hδ hδ', D.qjj_g hL (by omega) hb i₀ H hX,
    hs3, hs2]
  ring

end FlowSeq

/-! ### The hypotheses from `GoodCov2` and lattice symmetry -/

/-- `CovH` for a lattice-symmetric, symmetric covariance with `GoodCov2` at scale `j`. -/
theorem covH_of_good (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hjN : j + 1 < N) {ℓ : ℝ}
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 j ℓ C) (hCs : CSym C)
    (hsym : ∀ x y, C x y = C y x) : CovH C (L ^ (j + 1)) where
  htr x y t := hCs (AffAut.transl t) (IsGen.transl t) x y
  hsym := hsym
  hr x y h := hC.range hjN x y (by
    have : ((L ^ (j + 1) : ℕ) : ℝ) ≤ (supNorm (x - y) : ℝ) := by exact_mod_cast h.le
    push_cast at this
    have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ (j + 1) := by positivity
    linarith)
  h2r := by
    have hp : 2 ^ 3 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hL2 : 3 ≤ L := by norm_num at hp; omega
    have h1 : L ^ (j + 1) * L ≤ L ^ N := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) hjN
    have hLj : 1 ≤ L ^ (j + 1) := Nat.one_le_pow _ _ (by omega)
    nlinarith

theorem region_of_size (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hjN : j + 1 < N)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    ∀ x ∈ Bp (L := L) (N := N) j b,
      2 * (supNorm (x - base (Bp (L := L) (N := N) j b)) + L ^ (j + 1) + 4) < L ^ N := by
  intro x hx
  have hBp : IsSmall (j + 1) (Bp (L := L) (N := N) j b) := isSmall_clo (isSmall_blockSet_of_mem hb)
  have h1 := supNorm_nbhd_base hBp (subset_nbhd hBp.1 hx)
  have h2 := size_cond hL hjN
  have h3 : L ^ (j + 1) ≤ rad d L (j + 1) := by
    simp only [rad]; exact Nat.le_mul_of_pos_left _ (by positivity)
  have h4 : 2 ≤ pPhi d := by simp only [pPhi]; omega
  omega

namespace FlowSeq

variable (D : FlowSeq d L N)

/-- **`prop:C4b`(b), exact**, for lattice-symmetric, symmetric covariances with `GoodCov2`. -/
theorem kappaS_g' (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hjN : j + 1 < N)
    {ℓ : ℝ} (hC : ∀ i, GoodCov2 i ℓ (D.C i)) (hCs : CSym (D.C j))
    (hsym : ∀ x y, D.C j x y = D.C j y x) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) :
    ∃ δ : ℂ, cvec4 (blockSet (L := L) (N := N) j b) i₀
      (LS j (D.C j) (D.Vin j) (fun b' => sigE (D.s j) (D.Wlin j b')) b : Alg d L N) 3 =
      ∑ k ∈ range j, (D.κ k).g ^ 2 * D.beta j k b i₀ (eC 3) (eC 3) 3 +
        (D.κ j).g ^ 2 * D.betaQ j j b i₀ (eC 3) (eC 3) 3 +
        4 * (∑ x, (D.C j) x 0) * (D.κ j).g * ((D.κ j).nu + 2 * d * (D.κ j).g * δ) := by
  obtain ⟨c₀, δ, hc₀, hδ, hδ'⟩ := covProps hd hCs hsym
  exact ⟨δ, D.kappaS_g hd hL hjN hC hb i₀ (covH_of_good hL hjN (hC j) hCs hsym)
    (region_of_size hd hL hjN hb) hc₀ hδ hδ'⟩

end FlowSeq

end

end Step2
