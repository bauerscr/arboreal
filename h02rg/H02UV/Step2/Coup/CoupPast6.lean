import Step2.Coup.CoupG

/-!
# The past coefficients `b_{j,k}` (`h02uv-outline.tex`, `prop:C4b`(c))

For `k < j`,
`b_{j,k} = β_{j,k}(e_g, e_g)_g = (∏_{i=k+1}^{j} s_i⁶) mu4(𝓛_{C_j} ½ F_{C_k}(V_g(B_+), V_g(Λ))) / |B_+|`
(`FlowSeq.beta_past_eq`), where `C_i = C'_{i+1}` is the covariance of step `i`. Only the
degree-`6` part of the step-`k` source reaches the quartic coupling at step `j`. `σ_s` acts on it
by `s⁶`; the intermediate `𝔼θ` and `Loc` change only parts of degree `≤ 4`, which a further
contraction maps to degree `≤ 2`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

section General

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem coeff_neg'' (F : N Λ) {n : ℕ} (z : Fin n → Sf Λ) : coeff (-F) z = -coeff F z := by
  rw [← coeffL_apply, map_neg, coeffL_apply]

theorem coeff_sub'' (F G : N Λ) {n : ℕ} (z : Fin n → Sf Λ) :
    coeff (F - G) z = coeff F z - coeff G z := by
  rw [← coeffL_apply, map_sub, coeffL_apply, coeffL_apply]

/-- `(inv' F)_z = (-1)^n F_z` for `z` of length `n`. -/
theorem coeff_inv' (F : N Λ) : ∀ {n : ℕ} (z : Fin n → Sf Λ),
    coeff (inv' F) z = (-1) ^ n * coeff F z
  | 0, z => by rw [coeff_elim0, coeff_elim0, algebraMapInv_inv', pow_zero, one_mul]
  | n + 1, z => by
    rw [← Fin.cons_self_tail z, ← coeff_D, ← coeff_D, Grassmann.D_inv', coeff_neg'',
      coeff_inv' (D _ F), pow_succ]
    ring

theorem coeff_odd_of_even {F : N Λ} (hF : inv' F = F) {n : ℕ} (hn : Odd n)
    (z : Fin n → Sf Λ) : coeff F z = 0 := by
  have h := coeff_inv' F z
  rw [hF, hn.neg_one_pow] at h
  linear_combination h / 2

/-- `σ_s F - s⁶ F` has degree `≤ 4` for even `F` of degree `≤ 6`. -/
theorem degLe_sig_sub {F : N Λ} (hF : inv' F = F) (h6 : DegLe 6 F) (s : ℂ) :
    DegLe 4 (sig s F - s ^ 6 • F) := by
  intro m z hm
  rw [coeff_sub'', coeff_sig, coeff_smul]
  rcases (show m = 5 ∨ m = 6 ∨ 6 < m by omega) with rfl | rfl | h
  · rw [coeff_odd_of_even hF (by decide) z]; ring
  · ring
  · rw [h6 m z h]; ring

end General

variable {d L N : ℕ} [NeZero L]

/-! ### `mu4 ∘ 𝓛` only sees degree `6` -/

section MuL

variable (C : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ κ' : Fin d)

theorem mu4_lop_of_degLe {G : Alg d L N} (hG : DegLe 4 G) : mu4 b κ κ' (LopC C G) = 0 :=
  mu4_of_degLe ((hG.lop C).mono (by norm_num)) b κ κ'

theorem mu4_lop_sig {F : Alg d L N} (hF : inv' F = F) (h6 : DegLe 6 F) (s : ℂ) :
    mu4 b κ κ' (LopC C (sig s F)) = s ^ 6 * mu4 b κ κ' (LopC C F) := by
  have h := mu4_lop_of_degLe C b κ κ' (degLe_sig_sub hF h6 s)
  rw [map_sub, map_smul, mu4_sub, mu4_smul, sub_eq_zero] at h
  exact h

theorem mu4_lop_exp (C' : Matrix (Lam d L N) (Lam d L N) ℂ) {G : Alg d L N} (h6 : DegLe 6 G) :
    mu4 b κ κ' (LopC C (expLC C' G)) = mu4 b κ κ' (LopC C G) := by
  have h := mu4_lop_of_degLe C b κ κ' (h6.exp_sub C' (n := 4))
  rw [map_sub, mu4_sub, sub_eq_zero] at h
  exact h

theorem mu4_lop_loc (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    mu4 b κ κ' (LopC C (Loc2sXY X Y F)) = 0 :=
  mu4_lop_of_degLe C b κ κ' (degLe_Loc2sXY X Y F)

end MuL

/-! ### Regrouping blocks -/

theorem blocks_biUnion_succ {i : ℕ} {Y : Finset (Lam d L N)} (hY : IsPolymer (i + 1) Y) :
    (blocks (i + 1) Y).biUnion (fun c => blocks i (blockSet (L := L) (N := N) (i + 1) c)) =
      blocks i Y := by
  ext b
  simp only [mem_biUnion, mem_blocks]
  constructor
  · rintro ⟨c, ⟨y, hy, rfl⟩, x, hx, rfl⟩
    exact ⟨x, blockSet_subset_of_mem_blocks hY (mem_blocks.2 ⟨y, hy, rfl⟩) hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨blk (i + 1) x, ⟨x, hx, rfl⟩, x, mem_blockSet.2 rfl, rfl⟩

theorem sum_blocks_succ {M : Type*} [AddCommMonoid M] {i : ℕ} {Y : Finset (Lam d L N)}
    (hY : IsPolymer (i + 1) Y) (G : (Fin d → ℕ) → M) :
    ∑ c ∈ blocks (i + 1) Y, ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c), G b =
      ∑ b ∈ blocks i Y, G b := by
  rw [← blocks_biUnion_succ hY, sum_biUnion]
  intro c _ c' _ hcc'
  rw [Function.onFun, disjoint_left]
  intro b hb hb'
  obtain ⟨x, hx, rfl⟩ := mem_blocks.1 hb
  obtain ⟨x', hx', hxx'⟩ := mem_blocks.1 hb'
  apply hcc'
  rw [← mem_blockSet.1 hx, ← mem_blockSet.1 hx', blk_succ, blk_succ, hxx']

/-! ### The transport of the degree-`6` part -/

theorem even_coe (F : EvR (Lam d L N)) : inv' (F : Alg d L N) = F := mem_Ev.1 F.2

theorem degFam_TrL' {n : ℕ} (hn : 4 ≤ n) (i : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (s : ℂ)
    {F : Fam d L N} (hF : DegFam n F) : DegFam n (TrL i C s F) := by
  intro c
  simp only [TrL, LinearMap.coe_mk, AddHom.coe_mk, AddSubmonoidClass.coe_finsetSum,
    AddSubgroupClass.coe_sub, coe_Loc2E]
  refine DegLe.sum _ fun b _ => ?_
  have h := ((hF b).sig s).exp C
  rw [← coe_sigE, ← coe_EthE] at h
  exact h.sub ((degLe_Loc2sXY _ _ _).mono hn)

/-- **One transport multiplies the degree-`6` content by `s⁶`.** -/
theorem mu4_lop_TrL (C₂ : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ κ' : Fin d)
    {i : ℕ} (C : Matrix (Lam d L N) (Lam d L N) ℂ) (s : ℂ) {F : Fam d L N} (hF : DegFam 6 F)
    {Y : Finset (Lam d L N)} (hY : IsPolymer (i + 1) Y) :
    mu4 b κ κ' (LopC C₂ (∑ c ∈ blocks (i + 1) Y, (TrL i C s F c : Alg d L N))) =
      s ^ 6 * mu4 b κ κ' (LopC C₂ (∑ c ∈ blocks i Y, (F c : Alg d L N))) := by
  simp only [TrL, LinearMap.coe_mk, AddHom.coe_mk, AddSubmonoidClass.coe_finsetSum,
    AddSubgroupClass.coe_sub, coe_Loc2E, coe_EthE, coe_sigE, map_sum, map_sub, mu4_sum, mu4_sub,
    mu4_lop_loc, sub_zero]
  rw [sum_blocks_succ hY (fun b' => mu4 b κ κ' (LopC C₂ (expLC C (sig s (F b' : Alg d L N)))))]
  rw [mul_sum]
  refine sum_congr rfl fun b' _ => ?_
  rw [mu4_lop_exp C₂ b κ κ' C ((hF b').sig s), mu4_lop_sig C₂ b κ κ' (even_coe _) (hF b')]

/-- The source of step `k`, read through `mu4 ∘ 𝓛`. -/
theorem mu4_lop_SrcL (C₂ : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ κ' : Fin d)
    {k : ℕ} (C : Matrix (Lam d L N) (Lam d L N) ℂ) {Y : Finset (Lam d L N)}
    (hY : IsPolymer (k + 1) Y) (v : Fin 4 → ℂ) :
    mu4 b κ κ' (LopC C₂ (∑ c ∈ blocks (k + 1) Y,
      (SrcL k C (EthEL C) (VfamL k v) (VfamL k v) c : Alg d L N))) =
      mu4 b κ κ' (LopC C₂ ((1 / 2 : ℂ) • FC C (VcoupL Y v) (VcoupL univ v))) := by
  simp only [SrcL_apply, SrcFam, AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_sub,
    coe_Loc2E, map_sum, map_sub, mu4_sum, mu4_sub, mu4_lop_loc, sub_zero]
  rw [sum_blocks_succ hY (fun b' => mu4 b κ κ' (LopC C₂
    (SrcF k C (EthEL C) (VfamL k v) (VfamL k v) b' : Alg d L N)))]
  rw [← mu4_sum, ← map_sum]
  have hV : ∀ b', (VfamL (d := d) (L := L) (N := N) k v b' : Alg d L N) =
      VcoupL (blockSet k b') v := fun _ => rfl
  simp only [SrcF, EthEL_apply, Subalgebra.coe_smul, coe_FCE, coe_EthE,
    AddSubmonoidClass.coe_finsetSum, hV]
  rw [← smul_sum, ← FC_sum_left]
  -- replace `𝔼θ V` by `V`
  set A := ∑ b' ∈ blocks k Y, expLC C (VcoupL (blockSet (L := L) (N := N) k b') v)
  set B := ∑ b'' ∈ blockIdx (L := L) (N := N) k, expLC C (VcoupL (blockSet (L := L) (N := N) k b'') v)
  have hA : A = VcoupL Y v + (A - VcoupL Y v) := by abel
  have hB : B = VcoupL (univ : Finset (Lam d L N)) v + (B - VcoupL (univ : Finset (Lam d L N)) v) := by abel
  have hA2 : DegLe 2 (A - VcoupL Y v) := by
    rw [← sum_VcoupL_blocks (IsPolymer.of_succ hY) v, ← sum_sub_distrib]
    exact DegLe.sum _ fun b' _ => (degLe_VcoupL _ v).exp_sub C (n := 2)
  have hB2 : DegLe 2 (B - VcoupL (univ : Finset (Lam d L N)) v) := by
    have e : VcoupL (univ : Finset (Lam d L N)) v =
        ∑ b'' ∈ blockIdx (L := L) (N := N) k, VcoupL (blockSet (L := L) (N := N) k b'') v :=
      (sum_VcoupL_blocks (L := L) (N := N) (isPolymer_univ k) v).symm
    rw [e]
    simp only [B]
    rw [← sum_sub_distrib]
    exact DegLe.sum _ fun b' _ => (degLe_VcoupL _ v).exp_sub C (n := 2)
  have h4 := degLe_VcoupL (L := L) (N := N) Y v
  have h4' := degLe_VcoupL (L := L) (N := N) (univ : Finset (Lam d L N)) v
  have hcross : DegLe 4 (FC C A B - FC C (VcoupL Y v) (VcoupL (univ : Finset (Lam d L N)) v)) := by
    rw [hA, hB, FC_add_left, FC_add_right, FC_add_right]
    have e : ∀ X Y Z W : Alg d L N, X + Y + (Z + W) - X = Y + Z + W := by intros; abel
    rw [e]
    exact ((DegLe.fc (n := 2) (m := 0) C h4 hB2).add (DegLe.fc (n := 0) (m := 2) C hA2 h4')).add
      ((DegLe.fc (n := 0) (m := 0) C hA2 hB2).mono (by norm_num))
  have h := mu4_lop_of_degLe C₂ b κ κ' (hcross.smul (1 / 2 : ℂ))
  rw [smul_sub, map_sub, mu4_sub, sub_eq_zero] at h
  exact h

theorem isPolymer_of_le {m : ℕ} {Y : Finset (Lam d L N)} (hY : IsPolymer m Y) :
    ∀ k, k ≤ m → IsPolymer k Y := by
  induction m with
  | zero => intro k hk; obtain rfl : k = 0 := by omega
            exact hY
  | succ m ih =>
    intro k hk
    rcases (show k = m + 1 ∨ k ≤ m by omega) with rfl | h
    · exact hY
    · exact ih (IsPolymer.of_succ hY) k h

theorem degFam_SrcL6 (k : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (u v : Fin 4 → ℂ) :
    DegFam 6 (SrcL k C (EthEL C) (VfamL (L := L) (N := N) k u) (VfamL k v)) := by
  have hS : ∀ b', DegLe 6 (SrcF k C (EthEL C) (VfamL (L := L) (N := N) k u) (VfamL k v) b' :
      Alg d L N) := by
    intro b'
    simp only [SrcF, EthEL_apply, Subalgebra.coe_smul, coe_FCE, coe_EthE,
      AddSubmonoidClass.coe_finsetSum]
    exact (DegLe.fc (n := 2) (m := 2) C ((degLe_VcoupL _ u).exp C)
      (DegLe.sum _ fun b'' _ => (degLe_VcoupL _ v).exp C)).smul _
  intro c
  simp only [SrcL_apply, SrcFam, AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_sub,
    coe_Loc2E]
  exact DegLe.sum _ fun b _ => (hS b).sub ((degLe_Loc2sXY _ _ _).mono (by norm_num))

/-- **At the last step only `𝓛_{C} σ` of the degree-`6` part reaches the quartic coupling.** -/
theorem LpartL_g_eq (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j + 1 < N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (s : ℂ)
    (i₀ : Fin d) {F : Fam d L N} (hF : InF j F) (hdeg : DegFam 6 F)
    (hmu : ∀ c ii kk, mu4 (base (blockSet (L := L) (N := N) j c)) ii kk (F c : Alg d L N) = 0) :
    cvec4 (blockSet (L := L) (N := N) j b) i₀ (FlowSeq.LpartL j C s b F : Alg d L N) 3 =
      s ^ 6 * mu4 (base (Bp (L := L) (N := N) j b)) i₀ i₀
        (LopC C (∑ b' ∈ blocks j (Bp (L := L) (N := N) j b), (F b' : Alg d L N))) /
        (Bp (L := L) (N := N) j b).card := by
  have hsm := isSmall_blockSet_of_mem hb
  have hP := patch_of_small hL (by omega : j < N) hsm
  have hBp : IsSmall (j + 1) (Bp (L := L) (N := N) j b) := isSmall_clo hsm
  have hsize := size_cond hL hj
  have hrad := rad_le_succ (d := d) (L := L) j
  have hB0 : ((blockSet (L := L) (N := N) j b).card : ℂ) ≠ 0 := by
    exact_mod_cast hsm.2.1.1.card_pos.ne'
  have hterm : ∀ b' ∈ blocks j (Bp (L := L) (N := N) j b),
      mu4 (base (Bp (L := L) (N := N) j b)) i₀ i₀ (EthE C (sigE s (F b')) : Alg d L N) =
        s ^ 6 * mu4 (base (Bp (L := L) (N := N) j b)) i₀ i₀ (LopC C (F b' : Alg d L N)) := by
    intro b' hb'
    have hb'X : blockSet (L := L) (N := N) j b' ⊆ Bp j b :=
      blockSet_subset_of_mem_blocks (IsPolymer.of_succ hBp.1) hb'
    have hsm' := isSmall_blockSet_of_mem (mem_blockIdx_of_mem_blocks hb')
    have e1 : (EthE C (sigE s (F b')) : Alg d L N) = sig s (F b') + LopC C (sig s (F b')) +
        (expLC C (sig s (F b')) - sig s (F b') - LopC C (sig s (F b'))) := by
      rw [coe_EthE, coe_sigE]; abel
    have hd2 : DegLe 2 (expLC C (sig s (F b')) - sig s (F b') - LopC C (sig s (F b'))) :=
      ((hdeg b').sig s).exp_sub2 C (n := 2)
    rw [e1, mu4_add, mu4_add, mu4_of_degLe (hd2.mono (by norm_num)), add_zero,
      mu4_lop_sig C _ _ _ (even_coe _) (hdeg b'), mu4_sig]
    have hbase : base (blockSet (L := L) (N := N) j b') ∈ Bp (L := L) (N := N) j b :=
      hb'X (base_mem hsm'.2.1.1)
    have h2 := supNorm_nbhd_base hBp (subset_nbhd hBp.1 hbase)
    rw [mu4_base_indep (hF.loc b') (b := base (blockSet (L := L) (N := N) j b'))
      (fun x hx => by
        have h1 := supNorm_nbhd_base hsm' (Finset.mem_coe.1 hx)
        omega) i₀ i₀, hmu b' i₀ i₀]
    ring
  rw [cvec4_g]
  simp only [FlowSeq.LpartL, LinearMap.coe_mk, AddHom.coe_mk, coe_Loc2E]
  rw [Loc2sXY, mu4_add, mu4_LocXY, zero_add, Loc4sXY, mu4_sum]
  simp only [mu4_sum, mu4_smul, mu4_mono4Set hP]
  rw [sum_eq_single i₀ (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
  rw [sum_eq_single i₀ (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
  simp only [if_true, one_mul, AddSubmonoidClass.coe_finsetSum]
  rw [mu4_sum, sum_congr rfl hterm, ← mul_sum, map_sum, mu4_sum]
  field_simp

namespace FlowSeq

variable (D : FlowSeq d L N)

theorem degFam_TrIt {k : ℕ} {F : Fam d L N} (hF : DegFam 6 F) :
    ∀ n, DegFam 6 (D.TrIt k n F)
  | 0 => hF
  | n + 1 => by
    rw [TrIt_succ, LinearMap.comp_apply]
    exact degFam_TrL' (by norm_num) _ _ _ (degFam_TrIt hF n)

/-- **The transports multiply the degree-`6` content by `∏ s_i⁶`.** -/
theorem mu4_lop_TrIt (C₂ : Matrix (Lam d L N) (Lam d L N) ℂ) (b : Lam d L N) (κ κ' : Fin d)
    {k : ℕ} {F : Fam d L N} (hF : DegFam 6 F) :
    ∀ n {Y : Finset (Lam d L N)}, IsPolymer (k + 1 + n) Y →
      mu4 b κ κ' (LopC C₂ (∑ c ∈ blocks (k + 1 + n) Y, (D.TrIt k n F c : Alg d L N))) =
        (∏ i ∈ range n, D.s (k + 1 + i) ^ 6) *
          mu4 b κ κ' (LopC C₂ (∑ c ∈ blocks (k + 1) Y, (F c : Alg d L N)))
  | 0, Y, _ => by simp [TrIt]
  | n + 1, Y, hY => by
    rw [TrIt_succ, ← add_assoc]
    simp only [LinearMap.comp_apply]
    have hY' : IsPolymer (k + 1 + n + 1) Y := hY
    rw [mu4_lop_TrL (i := k + 1 + n) C₂ b κ κ' (D.C (k + 1 + n)) (D.s (k + 1 + n))
      (D.degFam_TrIt hF n) hY', mu4_lop_TrIt C₂ b κ κ' hF n (IsPolymer.of_succ hY'),
      prod_range_succ]
    ring

end FlowSeq

namespace FlowSeq

variable (D : FlowSeq d L N)

/-- Locality and vanishing own-block quartic pairing along the transports. -/
theorem trIt_loc (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) {k : ℕ} {ℓ : ℝ}
    (hC : ∀ i, k + 1 ≤ i → GoodCov2 i ℓ (D.C i)) {F : Fam d L N} (hF : InF (k + 1) F)
    (hmu : ∀ c ii kk, mu4 (base (blockSet (L := L) (N := N) (k + 1) c)) ii kk (F c : Alg d L N) = 0) :
    ∀ n, k + 1 + n < N → InF (k + 1 + n) (D.TrIt k n F) ∧
      ∀ c ii kk, mu4 (base (blockSet (L := L) (N := N) (k + 1 + n) c)) ii kk
        (D.TrIt k n F c : Alg d L N) = 0 := by
  intro n
  induction n with
  | zero => intro _; exact ⟨hF, hmu⟩
  | succ n ih =>
    intro hn
    obtain ⟨h1, -⟩ := ih (by omega)
    have hi : k + 1 + n + 1 < N := by omega
    have hL' : 2 ^ (d + 3) ≤ L := by omega
    rw [TrIt_succ, ← add_assoc, LinearMap.comp_apply]
    refine ⟨inF_TrL (i := k + 1 + n) (C := D.C (k + 1 + n)) hd hL' hi (hC _ (by omega)) _ h1, ?_⟩
    intro c ii kk
    exact mu4_TrL hL hi _ _ _ c ii kk

/-- **The past coefficients** (`prop:C4b`(c)): for `k < j`,
`b_{j,k} = (∏_{i=k+1}^{j} s_i⁶) mu4(𝓛_{C_j} ½ F_{C_k}(V_g(B_+), V_g(Λ))) / |B_+|`. -/
theorem beta_past_eq (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) {j k : ℕ} (hkj : k < j)
    (hjN : j + 1 < N) {ℓ : ℝ} (hC : ∀ i, k ≤ i → GoodCov2 i ℓ (D.C i)) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) :
    D.beta j k b i₀ (eC 3) (eC 3) 3 = (∏ i ∈ range (j - k), D.s (k + 1 + i) ^ 6) *
      mu4 (base (Bp (L := L) (N := N) j b)) i₀ i₀ (LopC (D.C j)
        ((1 / 2 : ℂ) • FC (D.C k) (VcoupL (Bp (L := L) (N := N) j b) (eC 3))
          (VcoupL univ (eC 3)))) / (Bp (L := L) (N := N) j b).card := by
  obtain ⟨n, rfl⟩ : ∃ n, j = k + 1 + n := ⟨j - k - 1, by omega⟩
  have hk1 : k + 1 < N := by omega
  set Src := SrcL k (D.C k) (EthEL (D.C k)) (VfamL (L := L) (N := N) k (eC 3)) (VfamL k (eC 3))
  have hInF : InF (k + 1) Src := inF_SrcL hd hL hk1 (hC k le_rfl) (eC 3)
  have hmu : ∀ c ii kk, mu4 (base (blockSet (L := L) (N := N) (k + 1) c)) ii kk
      (Src c : Alg d L N) = 0 := fun c ii kk => mu4_SrcL hL hk1 _ _ _ _ c ii kk
  have h6 : DegFam 6 Src := degFam_SrcL6 k (D.C k) _ _
  obtain ⟨hF, hmuF⟩ := D.trIt_loc hd hL (fun i hi => hC i (by omega)) hInF hmu n (by omega)
  have hBp : IsSmall (k + 1 + n + 1) (Bp (L := L) (N := N) (k + 1 + n) b) :=
    isSmall_clo (isSmall_blockSet_of_mem hb)
  have hY : IsPolymer (k + 1 + n) (Bp (L := L) (N := N) (k + 1 + n) b) := IsPolymer.of_succ hBp.1
  have hY1 : IsPolymer (k + 1) (Bp (L := L) (N := N) (k + 1 + n) b) :=
    isPolymer_of_le hY (k + 1) (by omega)
  have hkj' : k ≠ k + 1 + n := by omega
  unfold beta
  rw [if_neg hkj']
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply]
  rw [show k + 1 + n - 1 - k = n by omega]
  show cvec4 _ i₀ (LpartL (k + 1 + n) (D.C (k + 1 + n)) (D.s (k + 1 + n)) b (D.TrIt k n Src) :
    Alg d L N) 3 = _
  rw [LpartL_g_eq hL hjN hb _ _ i₀ hF (D.degFam_TrIt h6 n) hmuF,
    D.mu4_lop_TrIt _ _ _ _ h6 n hY, mu4_lop_SrcL _ _ _ _ _ hY1,
    show k + 1 + n - k = n + 1 by omega, prod_range_succ]
  ring

end FlowSeq

/-! ### The telescoping identity (`lem:F`(ii) under `mu4`) -/

/-- **`mu4 F_{C₁+C₂}(A', B') = mu4 F_{C₁}(A, B) + mu4 𝓛_{C₂} F_{C₁}(A, B) + mu4 F_{C₂}(A', B')`**
with `A' = e^{𝓛_{C₂}} A`, `B' = e^{𝓛_{C₂}} B`, for `A`, `B` of degree `≤ 4`. This is the exact form
of `𝔅(w + C') = 𝔅(w) + 2𝔅(w; C') + 𝔅(C')` behind the frozen comparison. -/
theorem mu4_FC_add_cov (C₁ C₂ : Matrix (Lam d L N) (Lam d L N) ℂ) {A B : Alg d L N}
    (hA : DegLe 4 A) (hB : DegLe 4 B) (b : Lam d L N) (κ κ' : Fin d) :
    mu4 b κ κ' (FC (C₁ + C₂) (expLC C₂ A) (expLC C₂ B)) =
      mu4 b κ κ' (FC C₁ A B) + mu4 b κ κ' (LopC C₂ (FC C₁ A B)) +
        mu4 b κ κ' (FC C₂ (expLC C₂ A) (expLC C₂ B)) := by
  have h6 : DegLe 6 (FC C₁ A B) := DegLe.fc (n := 2) (m := 2) C₁ hA hB
  have hd2 : DegLe 2 (expLC C₂ (FC C₁ A B) - FC C₁ A B - LopC C₂ (FC C₁ A B)) :=
    h6.exp_sub2 C₂ (n := 2)
  have e : expLC C₂ (FC C₁ A B) = FC C₁ A B + LopC C₂ (FC C₁ A B) +
      (expLC C₂ (FC C₁ A B) - FC C₁ A B - LopC C₂ (FC C₁ A B)) := by abel
  rw [FC_add_cov, mu4_add, e, mu4_add, mu4_add, mu4_of_degLe (hd2.mono (by norm_num)), add_zero]

end

end Step2
