import Step2.Coup.Degree

/-!
# The `g`-component of the past contributions (`h02uv-outline.tex`, `prop:C4b`(b))

For `k < j`, the `g`-component of `β_{j,k}(u, u)` is `u_g² β_{j,k}(e_g, e_g)_g`
(`FlowSeq.beta_past_g`). Equivalently, only the degree-`6` part of the step-`k` source, which
comes from `F(gM, gM)`, reaches the quartic coupling at a later step. The reasons:

* sources and transports have the form `∑_{B ⊆ B_+} (S(B) - Loc_{B_+,B} S(B_+))`, whose quartic
  pairing on `B_+` vanishes (`mu4_wpsum`);
* the quartic pairing does not depend on the base point for local polynomials
  (`mu4_base_indep`);
* for a source of degree `≤ 4`, `𝔼θ` and `σ` do not create new degree-`4` content
  (`DegLe.exp_sub`, `coeff_sig`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

/-! ### The rescaling on coefficients -/

section Sig

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- `(σ_r F)_z = r^n F_z` for `z` of length `n`. -/
theorem coeff_sig (r : ℂ) (F : N Λ) : ∀ {n : ℕ} (z : Fin n → Sf Λ),
    coeff (sig r F) z = r ^ n * coeff F z
  | 0, z => by rw [coeff_elim0, coeff_elim0, eps_sig, pow_zero, one_mul]
  | n + 1, z => by
    rw [← Fin.cons_self_tail z, ← coeff_D, ← coeff_D, D_sig, coeff_smul, coeff_sig r (D _ F),
      pow_succ]
    ring

theorem _root_.Grassmann.DegLe.sig {n : ℕ} {F : N Λ} (hF : DegLe n F) (r : ℂ) : DegLe n (sig r F) :=
  fun m z hm => by rw [coeff_sig, hF m z hm, mul_zero]

theorem sig_mem_NX {X : Set Λ} {F : N Λ} (hF : F ∈ NX X) (r : ℂ) : sig r F ∈ NX X := by
  refine Algebra.adjoin_induction (p := fun F _ => sig r F ∈ NX X) ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨⟨a, ha⟩, rfl⟩
    rw [sig_ψ]
    exact Subalgebra.smul_mem _ (ψ_mem_NX ha) _
  · intro c; rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ _
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro x y _ _ hx hy; rw [map_mul]; exact mul_mem hx hy

end Sig

variable {d L N : ℕ} [NeZero L]

theorem isSym_sig {F : Alg d L N} (hF : IsSym F) (r : ℂ) : IsSym (sig r F) :=
  fun n z hz => by rw [coeff_sig, hF n z hz, mul_zero]

theorem mu4_sig (b : Lam d L N) (i k : Fin d) (r : ℂ) (F : Alg d L N) :
    mu4 b i k (sig r F) = r ^ 4 * mu4 b i k F := by
  simp only [mu4, cf4, coeff_sig, mul_sum, mul_assoc]

/-! ### Sums of `(1 - Loc)` over the blocks of a block -/

theorem Bp_eq_of_mem {i : ℕ} {c b : Fin d → ℕ}
    (hb : b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c)) :
    Bp (L := L) (N := N) i b = blockSet (i + 1) c := by
  obtain ⟨x, hx, rfl⟩ := mem_blocks.1 hb
  rw [Bp, clo_blockSet (mem_blockIdx_of_mem_blocks hb), ← blk_succ, mem_blockSet.1 hx]

theorem unif_split (κ : ℂ) (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ) (Y : Finset (Lam d L N)) :
    unif κ c e Y = κ • (1 : Alg d L N) + unif 0 c e Y := by
  simp only [unif, zero_smul, zero_add, add_assoc]

/-- `Loc_{X,·}` is additive over disjoint unions. -/
theorem Loc2sXY_biUnion {ι : Type*} (s : Finset ι) (X : Finset (Lam d L N))
    (Y : ι → Finset (Lam d L N)) (hY : (s : Set ι).PairwiseDisjoint Y) (F : Alg d L N) :
    ∑ a ∈ s, Loc2sXY X (Y a) F = Loc2sXY X (s.biUnion Y) F := by
  simp only [Loc2sXY_eq_unif]
  rw [unif_split, sum_congr rfl fun a _ => unif_split _ _ _ _, sum_add_distrib, unif_sum _ _ _ _ _ hY,
    mul_zero, ← sum_smul, card_biUnion hY]
  push_cast
  rw [← sum_div, ← mul_sum]

theorem pairwiseDisjoint_blockSet' (i : ℕ) (s : Finset (Fin d → ℕ)) :
    (s : Set (Fin d → ℕ)).PairwiseDisjoint (blockSet (L := L) (N := N) i) := by
  intro b _ b' _ hbb'
  rw [Function.onFun, disjoint_left]
  intro x hx hx'
  exact hbb' ((mem_blockSet.1 hx).symm.trans (mem_blockSet.1 hx'))

/-- **The quartic pairing of `∑_{B ⊆ B_+} (G(B) - Loc_{B_+,B} ∑_{B'} G(B'))` on `B_+` vanishes.** -/
theorem mu4_wpsum (hL : 2 ^ (d + 3) + 8 * d < L) {i : ℕ} (hi : i + 1 < N) (c : Fin d → ℕ)
    (G : (Fin d → ℕ) → EvR (Lam d L N)) (ii kk : Fin d) :
    mu4 (base (blockSet (L := L) (N := N) (i + 1) c)) ii kk
      (∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c),
        ((G b : Alg d L N) - Loc2sXY (Bp (L := L) (N := N) i b) (blockSet i b)
          (∑ b' ∈ blocks i (Bp (L := L) (N := N) i b), (G b' : Alg d L N)))) = 0 := by
  by_cases hc : c ∈ blockIdx (L := L) (N := N) (i + 1)
  · have hsm := isSmall_blockSet_of_mem hc
    have hX := patch_of_small hL hi hsm
    have h2 : ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c),
        Loc2sXY (Bp (L := L) (N := N) i b) (blockSet i b)
          (∑ b' ∈ blocks i (Bp (L := L) (N := N) i b), (G b' : Alg d L N)) =
        ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c),
        Loc2sXY (blockSet (L := L) (N := N) (i + 1) c) (blockSet i b)
          (∑ b' ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c), (G b' : Alg d L N)) :=
      sum_congr rfl fun b hb => by rw [Bp_eq_of_mem hb]
    rw [sum_sub_distrib, h2, Loc2sXY_biUnion _ _ _ (pairwiseDisjoint_blockSet' i _),
      biUnion_blocks (IsPolymer.of_succ (isPolymer_blockSet (i + 1) c))]
    exact mu4_sub_Loc2sX hX hsm.2.1.1 _ ii kk
  · have hX0 : blockSet (L := L) (N := N) (i + 1) c = ∅ :=
      not_nonempty_iff_eq_empty.1 fun h => hc (mem_blockIdx.2 h)
    have : blocks i (blockSet (L := L) (N := N) (i + 1) c) = ∅ := by rw [hX0]; simp [blocks]
    rw [this, sum_empty]
    simp [mu4, cf4]

/-! ### Degree and locality of the transported polynomials -/

theorem degLe_mono4sSet (i k : Fin d) (Y : Finset (Lam d L N)) : DegLe 4 (mono4sSet i k Y) := by
  refine DegLe.sum _ fun x _ => ?_
  refine mono4s_cases i k x (DegLe 4) (fun _ _ => DegLe.add) (fun _ _ h h' => ?_)
    (fun c _ h => h.smul c) (fun e e' => ?_)
  · have := h.add (h'.smul (-1)); rwa [neg_one_smul, ← sub_eq_add_neg] at this
  · intro n z hn
    exact coeff_ιMulti_of_ne _ z (by omega)

theorem degLe_Loc2sXY (X Y : Finset (Lam d L N)) (F : Alg d L N) : DegLe 4 (Loc2sXY X Y F) := by
  rw [Loc2sXY_eq_unif, unif]
  refine ((DegLe.smul (degLe_one 4) _).add (DegLe.sum _ fun M _ =>
    ((degLe_monoSet M Y).mono (by norm_num)).smul _)).add ?_
  exact DegLe.sum _ fun i _ => DegLe.sum _ fun k _ => (degLe_mono4sSet i k Y).smul _

theorem _root_.Grassmann.DegLe.sub {Λ : Type*} [DecidableEq Λ] {n : ℕ} {x y : Grassmann.N Λ}
    (hx : DegLe n x) (hy : DegLe n y) : DegLe n (x - y) := by
  have := hx.add (hy.smul (-1)); rwa [neg_one_smul, ← sub_eq_add_neg] at this

/-- Families of degree `≤ n`. -/
def DegFam (n : ℕ) (F : Fam d L N) : Prop := ∀ c, DegLe n (F c : Alg d L N)

theorem inF_zero (j : ℕ) : InF (L := L) (N := N) j (0 : Fam d L N) :=
  ⟨fun _ => by simp [zero_mem], fun _ n z _ => by simp⟩

theorem inF_sig {j : ℕ} {F : Fam d L N} (hF : InF j F) (s : ℂ) :
    InF j (fun b => sigE s (F b)) :=
  ⟨fun b => by rw [coe_sigE]; exact sig_mem_NX (hF.loc b) s,
    fun b => by rw [coe_sigE]; exact isSym_sig (hF.sym b) s⟩

theorem inF_add {j : ℕ} {F G : Fam d L N} (hF : InF j F) (hG : InF j G) : InF j (F + G) :=
  ⟨fun b => by rw [Pi.add_apply, Subalgebra.coe_add]; exact add_mem (hF.loc b) (hG.loc b),
    fun b n z hz => by
      rw [Pi.add_apply, Subalgebra.coe_add, coeff_add, hF.sym b n z hz, hG.sym b n z hz, add_zero]⟩

theorem inF_smul {j : ℕ} {F : Fam d L N} (hF : InF j F) (r : ℂ) : InF j (r • F) :=
  ⟨fun b => by rw [Pi.smul_apply, Subalgebra.coe_smul]; exact Subalgebra.smul_mem _ (hF.loc b) _,
    fun b n z hz => by rw [Pi.smul_apply, Subalgebra.coe_smul, coeff_smul, hF.sym b n z hz,
      mul_zero]⟩

theorem inF_sub {j : ℕ} {F G : Fam d L N} (hF : InF j F) (hG : InF j G) : InF j (F - G) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ G]; exact inF_add hF (inF_smul hG _)

theorem TrL_eq_Wp (i : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (s : ℂ) (F : Fam d L N)
    (c : Fin d → ℕ) :
    TrL i C s F c = ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c),
      Wp i C 0 (fun b' => sigE s (F b')) b := by
  simp only [TrL, LinearMap.coe_mk, AddHom.coe_mk, Wp, Sb, LS, SX, Vpr, VprL, Pi.zero_apply,
    EthE_zero, sum_const_zero, FCE_zero_right, FCE_comm C 0, smul_zero, zero_add]

/-- **The transport keeps locality and `U(1)` symmetry.** -/
theorem inF_TrL (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {i : ℕ} (hi : i + 1 < N) {ℓ : ℝ}
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 i ℓ C) (s : ℂ) {F : Fam d L N}
    (hF : InF i F) : InF (i + 1) (TrL i C s F) := by
  constructor
  · intro c
    rw [TrL_eq_Wp, AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b hb => ?_
    have h := Wp_mem hd hL hi hC (inF_zero i) (inF_sig hF s) (mem_blockIdx_of_mem_blocks hb)
    rwa [NBp, Bp_eq_of_mem hb] at h
  · intro c
    rw [TrL_eq_Wp, AddSubmonoidClass.coe_finsetSum, isSym_iff_mem_SymS]
    exact Subalgebra.sum_mem _ fun b _ => Wp_sym (C := C) (inF_zero i) (inF_sig hF s) b

theorem degFam_TrL (i : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (s : ℂ) {F : Fam d L N}
    (hF : DegFam 4 F) : DegFam 4 (TrL i C s F) := by
  intro c
  simp only [TrL, LinearMap.coe_mk, AddHom.coe_mk, AddSubmonoidClass.coe_finsetSum,
    AddSubgroupClass.coe_sub, coe_Loc2E]
  refine DegLe.sum _ fun b _ => ?_
  have h := ((hF b).sig s).exp C
  rw [← coe_sigE, ← coe_EthE] at h
  exact h.sub (degLe_Loc2sXY _ _ _)

/-- The own-block quartic pairing of a transport vanishes. -/
theorem mu4_TrL (hL : 2 ^ (d + 3) + 8 * d < L) {i : ℕ} (hi : i + 1 < N)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) (s : ℂ) (F : Fam d L N) (c : Fin d → ℕ) (ii kk : Fin d) :
    mu4 (base (blockSet (L := L) (N := N) (i + 1) c)) ii kk (TrL i C s F c : Alg d L N) = 0 := by
  simp only [TrL, LinearMap.coe_mk, AddHom.coe_mk, AddSubmonoidClass.coe_finsetSum,
    AddSubgroupClass.coe_sub, coe_Loc2E]
  exact mu4_wpsum hL hi c (fun b => EthE C (sigE s (F b))) ii kk

theorem mu4_SrcL (hL : 2 ^ (d + 3) + 8 * d < L) {i : ℕ} (hi : i + 1 < N)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) (P : EvR (Lam d L N) →ₗ[ℂ] EvR (Lam d L N))
    (A B : Fam d L N) (c : Fin d → ℕ) (ii kk : Fin d) :
    mu4 (base (blockSet (L := L) (N := N) (i + 1) c)) ii kk (SrcL i C P A B c : Alg d L N) = 0 := by
  simp only [SrcL_apply, SrcFam, AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_sub,
    coe_Loc2E]
  exact mu4_wpsum hL hi c (fun b => SrcF i C P A B b) ii kk

/-! ### The source -/

theorem VcoupL_empty (v : Fin 4 → ℂ) : VcoupL (∅ : Finset (Lam d L N)) v = 0 := by
  simp [VcoupL, Vcoup, unif, monoSet, mono4sSet]

/-- A coupling polynomial on a small set is its own localisation. -/
theorem VcoupL_eq_Loc (hL : 2 ^ (d + 3) + 8 * d < L) {k : ℕ} (hk : k < N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) k) (v : Fin 4 → ℂ) :
    VcoupL (blockSet (L := L) (N := N) k b) v =
      Loc2sXY (blockSet k b) (blockSet k b) (VcoupL (blockSet (L := L) (N := N) k b) v) := by
  have hsm := isSmall_blockSet_of_mem hb
  have hX := patch_of_small hL hk hsm
  have hne := hsm.2.1.1
  have hX0 : ((blockSet (L := L) (N := N) k b).card : ℂ) ≠ 0 := by
    exact_mod_cast hne.card_pos.ne'
  have hV : VcoupL (blockSet (L := L) (N := N) k b) v =
      unif 0 (coupC (Coup.ofVec v)) (coupE (Coup.ofVec v)) (blockSet k b) := rfl
  rw [Loc2sXY_eq_unif, hV, eps_unif, locCoef_unif hX hne]
  congr 1
  · simp
  · funext i k'
    rw [mu4_unif hX, mul_div_assoc, div_self hX0, mul_one]

theorem inF_VfamL (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) {k : ℕ} (hk : k < N)
    (v : Fin 4 → ℂ) : InF (d := d) (L := L) (N := N) k (VfamL k v) := by
  constructor
  · intro b
    show VcoupL (blockSet (L := L) (N := N) k b) v ∈ _
    by_cases hb : b ∈ blockIdx (L := L) (N := N) k
    · rw [VcoupL_eq_Loc hL hk hb]
      exact Loc2XY_mem' hd (isPolymer_blockSet k b) _ _
    · rw [not_nonempty_iff_eq_empty.1 fun h => hb (mem_blockIdx.2 h), VcoupL_empty]
      exact zero_mem _
  · intro b
    show IsSym (VcoupL (blockSet (L := L) (N := N) k b) v)
    by_cases hb : b ∈ blockIdx (L := L) (N := N) k
    · rw [VcoupL_eq_Loc hL hk hb]; exact isSym_Loc2XY _ _ _
    · rw [not_nonempty_iff_eq_empty.1 fun h => hb (mem_blockIdx.2 h), VcoupL_empty]
      intro n z _; simp

theorem SrcL_eq_Wp (k : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : Fam d L N)
    (c : Fin d → ℕ) :
    SrcL k C (EthEL C) V V c = ∑ b ∈ blocks k (blockSet (L := L) (N := N) (k + 1) c),
      Wp k C V 0 b := by
  rw [SrcL_apply]
  exact sum_congr rfl fun b _ => (FlowSeq.Wp_zero_eq k C V b).symm

theorem inF_SrcL (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) {k : ℕ} (hk : k + 1 < N) {ℓ : ℝ}
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : GoodCov2 k ℓ C) (v : Fin 4 → ℂ) :
    InF (k + 1) (SrcL k C (EthEL C) (VfamL (L := L) (N := N) k v) (VfamL k v)) := by
  have hV := inF_VfamL (L := L) (N := N) hd hL (by omega : k < N) v
  have hL' : 2 ^ (d + 3) ≤ L := by omega
  constructor
  · intro c
    rw [SrcL_eq_Wp, AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ fun b hb => ?_
    have h := Wp_mem hd hL' hk hC hV (inF_zero k) (mem_blockIdx_of_mem_blocks hb)
    rwa [NBp, Bp_eq_of_mem hb] at h
  · intro c
    rw [SrcL_eq_Wp, AddSubmonoidClass.coe_finsetSum, isSym_iff_mem_SymS]
    exact Subalgebra.sum_mem _ fun b _ => Wp_sym (C := C) hV (inF_zero k) b

theorem degFam_SrcL (k : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) {u v : Fin 4 → ℂ}
    (huv : u 3 = 0 ∨ v 3 = 0) :
    DegFam 4 (SrcL k C (EthEL C) (VfamL (L := L) (N := N) k u) (VfamL k v)) := by
  have hS : ∀ b', DegLe 4 (SrcF k C (EthEL C) (VfamL (L := L) (N := N) k u) (VfamL k v) b' :
      Alg d L N) := by
    intro b'
    simp only [SrcF, EthEL_apply, Subalgebra.coe_smul, coe_FCE, coe_EthE,
      AddSubmonoidClass.coe_finsetSum]
    refine DegLe.smul ?_ _
    rcases huv with hu | hv
    · exact DegLe.fc (n := 0) (m := 2) C ((degLe_VcoupL_quad _ hu).exp C)
        (DegLe.sum _ fun b'' _ => (degLe_VcoupL _ v).exp C)
    · exact DegLe.fc (n := 2) (m := 0) C ((degLe_VcoupL _ u).exp C)
        (DegLe.sum _ fun b'' _ => (degLe_VcoupL_quad _ hv).exp C)
  intro c
  simp only [SrcL_apply, SrcFam, AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_sub,
    coe_Loc2E]
  exact DegLe.sum _ fun b _ => (hS b).sub (degLe_Loc2sXY _ _ _)

/-! ### The `g`-component at the last step -/

theorem rad_le_succ (j : ℕ) : rad d L j ≤ rad d L (j + 1) := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  simp only [rad, pow_succ]
  exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hL)

/-- **At the last step only the contractions reach the quartic coupling**: if `F` is local, of
degree `≤ 4`, and has vanishing quartic pairing on its own blocks, then the `g`-component of
`Loc_{B_+,B} ∑ 𝔼θ σ F` vanishes. -/
theorem LpartL_g_zero (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j + 1 < N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (s : ℂ)
    (i₀ : Fin d) {F : Fam d L N} (hF : InF j F) (hdeg : DegFam 4 F)
    (hmu : ∀ c ii kk, mu4 (base (blockSet (L := L) (N := N) j c)) ii kk (F c : Alg d L N) = 0) :
    cvec4 (blockSet (L := L) (N := N) j b) i₀ (FlowSeq.LpartL j C s b F : Alg d L N) 3 = 0 := by
  have hsm := isSmall_blockSet_of_mem hb
  have hBp : IsSmall (j + 1) (Bp (L := L) (N := N) j b) := isSmall_clo hsm
  have hsize := size_cond hL hj
  have hrad := rad_le_succ (d := d) (L := L) j
  have hH : ∀ ii kk, mu4 (base (Bp (L := L) (N := N) j b)) ii kk
      (∑ b' ∈ blocks j (Bp (L := L) (N := N) j b), (EthE C (sigE s (F b')) : Alg d L N)) = 0 := by
    intro ii kk
    rw [mu4_sum]
    refine sum_eq_zero fun b' hb' => ?_
    have hb'X : blockSet (L := L) (N := N) j b' ⊆ Bp j b :=
      blockSet_subset_of_mem_blocks (IsPolymer.of_succ hBp.1) hb'
    have hsm' := isSmall_blockSet_of_mem (mem_blockIdx_of_mem_blocks hb')
    have e1 : (EthE C (sigE s (F b')) : Alg d L N) =
        sig s (F b') + (expLC C (sig s (F b')) - sig s (F b')) := by
      rw [coe_EthE, coe_sigE]; abel
    have hd2 : DegLe 2 (expLC C (sig s (F b')) - sig s (F b')) :=
      ((hdeg b').sig s).exp_sub C
    rw [e1, mu4_add, mu4_of_degLe (hd2.mono (by norm_num)), add_zero, mu4_sig]
    have hbase : base (blockSet (L := L) (N := N) j b') ∈ Bp (L := L) (N := N) j b :=
      hb'X (base_mem hsm'.2.1.1)
    have h2 := supNorm_nbhd_base hBp (subset_nbhd hBp.1 hbase)
    rw [mu4_base_indep (hF.loc b') (b := base (blockSet (L := L) (N := N) j b'))
      (fun x hx => by
        have h1 := supNorm_nbhd_base hsm' (Finset.mem_coe.1 hx)
        omega) ii kk, hmu b' ii kk, mul_zero]
  rw [cvec4_g]
  simp only [FlowSeq.LpartL, LinearMap.coe_mk, AddHom.coe_mk, coe_Loc2E,
    AddSubmonoidClass.coe_finsetSum]
  rw [Loc2sXY, mu4_add, mu4_LocXY, zero_add, Loc4sXY]
  simp only [hH, zero_div, zero_smul, sum_const_zero]
  simp [mu4, cf4]

theorem degFam_add {n : ℕ} {F G : Fam d L N} (hF : DegFam n F) (hG : DegFam n G) :
    DegFam n (F + G) := fun c => by
  rw [Pi.add_apply, Subalgebra.coe_add]; exact (hF c).add (hG c)

theorem degFam_smul {n : ℕ} {F : Fam d L N} (hF : DegFam n F) (r : ℂ) : DegFam n (r • F) :=
  fun c => by rw [Pi.smul_apply, Subalgebra.coe_smul]; exact (hF c).smul r

namespace FlowSeq

variable (D : FlowSeq d L N)

theorem TrIt_succ (k n : ℕ) :
    D.TrIt k (n + 1) = TrL (k + 1 + n) (D.C (k + 1 + n)) (D.s (k + 1 + n)) ∘ₗ D.TrIt k n := rfl

/-- **The transports keep locality, degree `≤ 4` and the vanishing own-block quartic pairing.** -/
theorem trIt_props (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) {k : ℕ} {ℓ : ℝ}
    (hC : ∀ i, k + 1 ≤ i → GoodCov2 i ℓ (D.C i)) {F : Fam d L N} (hF : InF (k + 1) F)
    (hdeg : DegFam 4 F)
    (hmu : ∀ c ii kk, mu4 (base (blockSet (L := L) (N := N) (k + 1) c)) ii kk (F c : Alg d L N) = 0) :
    ∀ n, k + 1 + n < N → InF (k + 1 + n) (D.TrIt k n F) ∧ DegFam 4 (D.TrIt k n F) ∧
      ∀ c ii kk, mu4 (base (blockSet (L := L) (N := N) (k + 1 + n) c)) ii kk
        (D.TrIt k n F c : Alg d L N) = 0 := by
  intro n
  induction n with
  | zero => intro _; exact ⟨hF, hdeg, hmu⟩
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2, -⟩ := ih (by omega)
    have hi : k + 1 + n + 1 < N := by omega
    have hL' : 2 ^ (d + 3) ≤ L := by omega
    rw [TrIt_succ, ← add_assoc, LinearMap.comp_apply]
    refine ⟨inF_TrL (i := k + 1 + n) (C := D.C (k + 1 + n)) hd hL' hi (hC _ (by omega)) _ h1,
      degFam_TrL _ _ _ h2, ?_⟩
    intro c ii kk
    exact mu4_TrL hL hi _ _ _ c ii kk

/-- **`prop:C4b`(b) for the past steps**: for `k < j`,
`β_{j,k}(u, u)_g = u_g² β_{j,k}(e_g, e_g)_g`. -/
theorem beta_past_g (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) {j k : ℕ} (hkj : k < j)
    (hjN : j + 1 < N) {ℓ : ℝ} (hC : ∀ i, k ≤ i → GoodCov2 i ℓ (D.C i)) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) (u : Fin 4 → ℂ) :
    D.beta j k b i₀ u u 3 = u 3 ^ 2 * D.beta j k b i₀ (Pi.single 3 1) (Pi.single 3 1) 3 := by
  obtain ⟨n, rfl⟩ : ∃ n, j = k + 1 + n := ⟨j - k - 1, by omega⟩
  set eg : Fin 4 → ℂ := Pi.single 3 1
  set uq : Fin 4 → ℂ := u - u 3 • eg
  have huq : uq 3 = 0 := by simp [uq, eg]
  have heg : eg 3 = 1 := by simp [eg]
  have hu : VfamL (d := d) (L := L) (N := N) k u = VfamL k uq + u 3 • VfamL k eg := by
    rw [← map_smul, ← map_add]; congr 1; simp [uq]
  set P := EthEL (D.C k)
  set Src := SrcL k (D.C k) P
  set Dsrc : Fam d L N := Src (VfamL k u) (VfamL k u) - u 3 ^ 2 • Src (VfamL k eg) (VfamL k eg)
  have hD : Dsrc = Src (VfamL k uq) (VfamL k uq) + u 3 • Src (VfamL k uq) (VfamL k eg) +
      u 3 • Src (VfamL k eg) (VfamL k uq) := by
    simp only [Dsrc, hu, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    module
  have hk1 : k + 1 < N := by omega
  have hInF : InF (k + 1) Dsrc :=
    inF_sub (inF_SrcL hd hL hk1 (hC k le_rfl) u) (inF_smul (inF_SrcL hd hL hk1 (hC k le_rfl) eg) _)
  have hdeg : DegFam 4 Dsrc := by
    rw [hD]
    exact degFam_add (degFam_add (degFam_SrcL k _ (Or.inl huq))
      (degFam_smul (degFam_SrcL k _ (Or.inl huq)) _)) (degFam_smul (degFam_SrcL k _ (Or.inr huq)) _)
  have hmu : ∀ c ii kk, mu4 (base (blockSet (L := L) (N := N) (k + 1) c)) ii kk
      (Dsrc c : Alg d L N) = 0 := by
    intro c ii kk
    simp only [Dsrc, Pi.sub_apply, Pi.smul_apply, AddSubgroupClass.coe_sub, Subalgebra.coe_smul,
      mu4_sub, mu4_smul, Src, mu4_SrcL hL hk1, mul_zero, sub_zero]
  obtain ⟨h1, h2, h3⟩ := D.trIt_props hd hL (fun i hi => hC i (by omega)) hInF hdeg hmu n (by omega)
  have hzero := LpartL_g_zero hL hjN hb (D.C (k + 1 + n)) (D.s (k + 1 + n)) i₀ h1 h2 h3
  have hkj' : k ≠ k + 1 + n := by omega
  unfold beta
  rw [if_neg hkj']
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply]
  rw [show k + 1 + n - 1 - k = n by omega]
  have e := hzero
  simp only [Dsrc, map_sub, map_smul, AddSubgroupClass.coe_sub, Subalgebra.coe_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
  simp only [AlgHom.toLinearMap_apply, Subalgebra.coe_val]
  linear_combination e

end FlowSeq

end

end Step2
