import Step2.Coup.V0Sym

/-!
# The quadratic structure of `κ_S` (`h02uv-outline.tex`, Proposition `prop:C4b`(a))

Over several steps, with covariances `C k`, rescalings `s k` and input couplings `κ k`, the
*linearised* remainder `𝒲^lin` is
`𝒲^lin_0 = 0` and `𝒲^lin_{k+1}(B_+) = ∑_{B ⊆ B_+} 𝒲'_k(B)`, where `𝒲'_k = Wp k (C k) V_{κ k} (σ_{s k} 𝒲^lin_k)`.
The actual `Wnext2` uses `∏ (1 + 𝒲') - 1` instead; the difference consists of products of at
least two `𝒲'`, which are of order `≥ 4` in the couplings.

`kappaS_quad`: the coefficient vector of `Loc_{B_+,B} S_j(B_+)` is
`∑_{k ≤ j} β_{j,k}(κ_k, κ_k)`, for bilinear maps `β_{j,k} : ℂ⁴ × ℂ⁴ → ℂ⁴` that depend only on
`C k, …, C j` and `s (k+1), …, s j`.

The pieces:
* `cvec4`: the coefficient vector `(z, y, ν, g)` of a polynomial on a patch, linear, and equal to
  `κ` on `V_κ` (`cvec4_unif`);
* `VcoupL`: `κ ↦ V_κ(Y)` as a linear map on `ℂ⁴` (`Vcoup_eq_VcoupL`);
* `TrL`: the linear transport `𝒲 ↦ ∑_{B ⊆ B_+} (𝔼θ σ 𝒲(B) - Loc_{B_+,B} 𝔼θ σ 𝒲(B_+))`;
* `SrcL`: the bilinear source `(A, B) ↦ ∑_{B ⊆ B_+} (1 - Loc) ½ F(𝔼θ A, 𝔼θ B(Λ))`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-! ### Coefficient vectors -/

theorem locCoef_add (X : Finset (Lam d L N)) (F G : Alg d L N) :
    locCoef X (F + G) = locCoef X F + locCoef X G := by
  unfold locCoef
  rw [← Matrix.add_vecMul]
  congr 1
  funext β
  exact mu_add _ _ _ _

theorem locCoef_smul (X : Finset (Lam d L N)) (r : ℂ) (F : Alg d L N) :
    locCoef X (r • F) = r • locCoef X F := by
  unfold locCoef
  rw [← Matrix.smul_vecMul]
  congr 1
  funext β
  exact mu_smul _ _ _ _

/-- The coefficient vector `(z, y, ν, g)` of a polynomial on `X`, read off in direction `i₀`. -/
def cvec4 (X : Finset (Lam d L N)) (i₀ : Fin d) : Alg d L N →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun F := ![locCoef X F (.m2 i₀ i₀), -2 * locCoef X F (.a2 s(i₀, i₀)), locCoef X F .c,
    mu4 (base X) i₀ i₀ F / X.card]
  map_add' F G := by
    funext a
    fin_cases a <;> simp [locCoef_add, mu4_add, add_div] <;> ring
  map_smul' r F := by
    funext a
    fin_cases a <;> simp [locCoef_smul, mu4_smul, mul_div_assoc] <;> ring

/-- The vector of a coupling. -/
def Coup.toVec (κ : Coup) : Fin 4 → ℂ := ![κ.z, κ.y, κ.nu, κ.g]

/-- The coupling of a vector. -/
def Coup.ofVec (v : Fin 4 → ℂ) : Coup := ⟨v 0, v 1, v 2, v 3⟩

theorem Coup.ofVec_toVec (κ : Coup) : Coup.ofVec κ.toVec = κ := rfl

/-- **`cvec4` reads off the coupling vector.** -/
theorem cvec4_unif {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty) (i₀ : Fin d)
    (r : ℂ) (κ : Coup) : cvec4 X i₀ (unif r (coupC κ) (coupE κ) X) = κ.toVec := by
  have hX0 : (X.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  funext a
  fin_cases a <;>
    simp [cvec4, Coup.toVec, locCoef_unif hX hne, mu4_unif hX, coupC, coupE, hX0] <;> ring

/-! ### `V_κ` is linear in `κ` -/

theorem unif_smul' (r κ : ℂ) (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ) (Y : Finset (Lam d L N)) :
    r • unif κ c e Y = unif (r * κ) (fun M => r * c M) (fun i k => r * e i k) Y := by
  simp only [unif, smul_add, smul_sum, smul_smul]

/-- `κ ↦ V_κ(Y)` on `ℂ⁴`. -/
def VcoupL (Y : Finset (Lam d L N)) : (Fin 4 → ℂ) →ₗ[ℂ] Alg d L N where
  toFun v := Vcoup (Coup.ofVec v) Y
  map_add' v w := by
    simp only [Vcoup, unif_add]
    congr 1
    · simp
    · funext M
      cases M <;> simp [coupC, Coup.ofVec] <;> split_ifs <;> ring
    · funext i k
      simp only [coupE, Coup.ofVec, Pi.add_apply]
      split_ifs <;> ring
  map_smul' c v := by
    simp only [Vcoup, RingHom.id_apply, unif_smul']
    congr 1
    · simp
    · funext M
      cases M <;> simp [coupC, Coup.ofVec] <;> split_ifs <;> ring
    · funext i k
      simp only [coupE, Coup.ofVec, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> ring

theorem unif_mem_Ev (κ : ℂ) (c : Mono d → ℂ) (e : Fin d → Fin d → ℂ) (Y : Finset (Lam d L N)) :
    unif κ c e Y ∈ Ev (Lam d L N) := by
  refine add_mem (add_mem (Subalgebra.smul_mem _ (one_mem _) _) ?_) ?_
  · exact Subalgebra.sum_mem _ fun M _ => Subalgebra.smul_mem _
      (Subalgebra.sum_mem _ fun x _ => monoAt_mem_Ev M x) _
  · exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun k _ =>
      Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun x _ => mono4_mem_Ev i k x) _

/-- The coupling family `B ↦ V_v(B)` at scale `k`, linear in `v ∈ ℂ⁴`. -/
def VfamL (k : ℕ) : (Fin 4 → ℂ) →ₗ[ℂ] Fam d L N where
  toFun v b := ⟨VcoupL (blockSet (L := L) (N := N) k b) v, unif_mem_Ev _ _ _ _⟩
  map_add' v w := by funext b; exact Subtype.ext (map_add _ _ _)
  map_smul' c v := by funext b; exact Subtype.ext (map_smul _ _ _)

theorem coe_VfamL (k : ℕ) (κ : Coup) (b : Fin d → ℕ) :
    (VfamL (L := L) (N := N) k κ.toVec b : Alg d L N) = Vcoup κ (blockSet k b) := rfl

/-! ### The linear transport and the bilinear source -/

theorem FCE_add_left' {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)
    (A A' B : EvR Λ) : FCE C (A + A') B = FCE C A B + FCE C A' B := by
  rw [FCE_comm, FCE_add_right, FCE_comm C B, FCE_comm C B]

/-- `𝒲 ↦ ∑_{B ⊆ B_+} (𝔼θ σ_s 𝒲(B) - Loc_{B_+,B} ∑_{B' ⊆ B_+} 𝔼θ σ_s 𝒲(B'))`, from scale `i`
to scale `i + 1`. -/
def TrL (i : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (s : ℂ) : Fam d L N →ₗ[ℂ] Fam d L N where
  toFun F c := ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c),
    (EthE C (sigE s (F b)) - Loc2E (Bp (L := L) (N := N) i b) (blockSet i b)
      (∑ b' ∈ blocks i (Bp (L := L) (N := N) i b), EthE C (sigE s (F b'))))
  map_add' F G := by
    funext c
    simp only [Pi.add_apply, map_add, EthE_add, sum_add_distrib, Loc2E_add]
    rw [← sum_add_distrib]
    exact sum_congr rfl fun b _ => by abel
  map_smul' r F := by
    funext c
    simp only [Pi.smul_apply, map_smul, EthE_smul, RingHom.id_apply]
    rw [smul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [← smul_sum, Loc2E_smul, smul_sub]

/-- `𝔼_C θ` as a linear map. -/
def EthEL (C : Matrix (Lam d L N) (Lam d L N) ℂ) : EvR (Lam d L N) →ₗ[ℂ] EvR (Lam d L N) where
  toFun := EthE C
  map_add' := EthE_add C
  map_smul' := EthE_smul C

theorem EthEL_apply (C : Matrix (Lam d L N) (Lam d L N) ℂ) (F : EvR (Lam d L N)) :
    EthEL C F = EthE C F := rfl

/-- The bilinear source `(A, B) ↦ ½ F_C(P A(B), ∑_{B''} P B(B''))`, with a linear pre-map `P`
(`P = 𝔼_C θ` for the step, `P = id` for the reformulation in terms of `κ'`). -/
def SrcF (i : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (P : EvR (Lam d L N) →ₗ[ℂ] EvR (Lam d L N)) (A B : Fam d L N) (b : Fin d → ℕ) :
    EvR (Lam d L N) :=
  (1 / 2 : ℂ) • FCE C (P (A b)) (∑ b'' ∈ blockIdx (L := L) (N := N) i, P (B b''))

section SrcFLin

variable (i : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (P : EvR (Lam d L N) →ₗ[ℂ] EvR (Lam d L N))

theorem SrcF_add_left (A A' B : Fam d L N) b :
    SrcF i C P (A + A') B b = SrcF i C P A B b + SrcF i C P A' B b := by
  simp only [SrcF, Pi.add_apply, map_add, FCE_add_left', smul_add]

theorem SrcF_add_right (A B B' : Fam d L N) b :
    SrcF i C P A (B + B') b = SrcF i C P A B b + SrcF i C P A B' b := by
  simp only [SrcF, Pi.add_apply, map_add, sum_add_distrib, FCE_add_right, smul_add]

theorem SrcF_smul_left (r : ℂ) (A B : Fam d L N) b :
    SrcF i C P (r • A) B b = r • SrcF i C P A B b := by
  simp only [SrcF, Pi.smul_apply, map_smul, FCE_smul_left, smul_comm r]

theorem SrcF_smul_right (r : ℂ) (A B : Fam d L N) b :
    SrcF i C P A (r • B) b = r • SrcF i C P A B b := by
  simp only [SrcF, Pi.smul_apply, map_smul, ← smul_sum, FCE_smul_right, smul_comm r]

/-- The family form of the source: `(1 - Loc)` applied to `SrcF`, summed over `B ⊆ B_+`. -/
def SrcFam (A B : Fam d L N) : Fam d L N :=
  fun c => ∑ b ∈ blocks i (blockSet (L := L) (N := N) (i + 1) c),
    (SrcF i C P A B b - Loc2E (Bp (L := L) (N := N) i b) (blockSet i b)
      (∑ b' ∈ blocks i (Bp (L := L) (N := N) i b), SrcF i C P A B b'))

theorem SrcFam_add_left (A A' B : Fam d L N) :
    SrcFam i C P (A + A') B = SrcFam i C P A B + SrcFam i C P A' B := by
  funext c
  simp only [SrcFam, Pi.add_apply, SrcF_add_left, sum_add_distrib, Loc2E_add]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun b _ => by abel

theorem SrcFam_add_right (A B B' : Fam d L N) :
    SrcFam i C P A (B + B') = SrcFam i C P A B + SrcFam i C P A B' := by
  funext c
  simp only [SrcFam, Pi.add_apply, SrcF_add_right, sum_add_distrib, Loc2E_add]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun b _ => by abel

theorem SrcFam_smul_left (r : ℂ) (A B : Fam d L N) :
    SrcFam i C P (r • A) B = r • SrcFam i C P A B := by
  funext c
  simp only [SrcFam, Pi.smul_apply, SrcF_smul_left]
  rw [smul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [← smul_sum, Loc2E_smul, smul_sub]

theorem SrcFam_smul_right (r : ℂ) (A B : Fam d L N) :
    SrcFam i C P A (r • B) = r • SrcFam i C P A B := by
  funext c
  simp only [SrcFam, Pi.smul_apply, SrcF_smul_right]
  rw [smul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [← smul_sum, Loc2E_smul, smul_sub]

/-- The bilinear source. -/
def SrcL : Fam d L N →ₗ[ℂ] Fam d L N →ₗ[ℂ] Fam d L N :=
  LinearMap.mk₂ ℂ (SrcFam i C P) (SrcFam_add_left i C P) (SrcFam_smul_left i C P)
    (SrcFam_add_right i C P) (SrcFam_smul_right i C P)

theorem SrcL_apply (A B : Fam d L N) : SrcL i C P A B = SrcFam i C P A B := rfl

end SrcFLin

/-! ### The linearised recursion -/

/-- The data of several steps: covariances, rescalings and input couplings. -/
structure FlowSeq (d L N : ℕ) [NeZero L] where
  C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ
  s : ℕ → ℂ
  κ : ℕ → Coup

namespace FlowSeq

variable (D : FlowSeq d L N)

/-- The input potential at step `k`. -/
def Vin (k : ℕ) : Fam d L N := VfamL k (D.κ k).toVec

/-- The linearised remainder: `𝒲^lin_{k+1}(B_+) = ∑_{B ⊆ B_+} Wp k (C k) V_k (σ 𝒲^lin_k) B`. -/
def Wlin : ℕ → Fam d L N
  | 0 => 0
  | k + 1 => fun c => ∑ b ∈ blocks k (blockSet (L := L) (N := N) (k + 1) c),
      Wp k (D.C k) (D.Vin k) (fun b' => sigE (D.s k) (Wlin k b')) b

theorem Wp_zero_eq (k : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : Fam d L N)
    (b : Fin d → ℕ) :
    Wp k C V 0 b = SrcF k C (EthEL C) V V b - Loc2E (Bp (L := L) (N := N) k b) (blockSet k b)
      (∑ b' ∈ blocks k (Bp (L := L) (N := N) k b), SrcF k C (EthEL C) V V b') := by
  simp only [Wp, Sb, LS, SX, Pi.zero_apply, EthE_zero, add_zero, SrcF, Vpr, VprL, EthEL_apply]

theorem Wlin_succ (k : ℕ) :
    D.Wlin (k + 1) = SrcL k (D.C k) (EthEL (D.C k)) (D.Vin k) (D.Vin k) + TrL k (D.C k) (D.s k) (D.Wlin k) := by
  funext c
  simp only [Wlin, Pi.add_apply, SrcL_apply, SrcFam, TrL, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [Wp_split, Wp_zero_eq]

/-- The transport from scale `k + 1` to scale `k + 1 + n`. -/
def TrIt (k : ℕ) : ℕ → (Fam d L N →ₗ[ℂ] Fam d L N)
  | 0 => LinearMap.id
  | n + 1 => TrL (k + 1 + n) (D.C (k + 1 + n)) (D.s (k + 1 + n)) ∘ₗ TrIt k n

/-- **`𝒲^lin_j = ∑_{k<j} T_{j,k} Src_k`**: the contribution of step `k` is its source, transported. -/
theorem Wlin_eq (j : ℕ) :
    D.Wlin j = ∑ k ∈ range j, D.TrIt k (j - 1 - k) (SrcL k (D.C k) (EthEL (D.C k)) (D.Vin k) (D.Vin k)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Wlin_succ, ih, map_sum, sum_range_succ, add_comm]
    congr 1
    · refine sum_congr rfl fun k hk => ?_
      obtain ⟨n, rfl⟩ : ∃ n, j = k + 1 + n := ⟨j - 1 - k, by have := mem_range.1 hk; omega⟩
      rw [show k + 1 + n + 1 - 1 - k = n + 1 by omega, show k + 1 + n - 1 - k = n by omega]
      rfl
    · rw [show j + 1 - 1 - j = 0 by omega]; rfl

/-! ### `Loc S_j` -/

/-- `𝒲 ↦ Loc_{B_+,B} ∑_{B' ⊆ B_+} 𝔼θ σ_s 𝒲(B')`. -/
def LpartL (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (s : ℂ) (b : Fin d → ℕ) :
    Fam d L N →ₗ[ℂ] EvR (Lam d L N) where
  toFun F := Loc2E (Bp (L := L) (N := N) j b) (blockSet j b)
    (∑ b' ∈ blocks j (Bp (L := L) (N := N) j b), EthE C (sigE s (F b')))
  map_add' F G := by
    simp only [Pi.add_apply, map_add, EthE_add, sum_add_distrib, Loc2E_add]
  map_smul' r F := by
    simp only [Pi.smul_apply, map_smul, EthE_smul, ← smul_sum, Loc2E_smul, RingHom.id_apply]

/-- `(A, B) ↦ Loc_{B_+,B} ∑_{B' ⊆ B_+} ½ F(P A(B'), P B(Λ))`. -/
def LS0 (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (P : EvR (Lam d L N) →ₗ[ℂ] EvR (Lam d L N))
    (b : Fin d → ℕ) (A B : Fam d L N) : EvR (Lam d L N) :=
  Loc2E (Bp (L := L) (N := N) j b) (blockSet j b)
    (∑ b' ∈ blocks j (Bp (L := L) (N := N) j b), SrcF j C P A B b')

/-- `LS0` as a bilinear map. -/
def LS0L (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (P : EvR (Lam d L N) →ₗ[ℂ] EvR (Lam d L N))
    (b : Fin d → ℕ) : Fam d L N →ₗ[ℂ] Fam d L N →ₗ[ℂ] EvR (Lam d L N) :=
  LinearMap.mk₂ ℂ (LS0 j C P b)
    (fun A A' B => by simp only [LS0, SrcF_add_left, sum_add_distrib, Loc2E_add])
    (fun r A B => by simp only [LS0, SrcF_smul_left, ← smul_sum, Loc2E_smul])
    (fun A B B' => by simp only [LS0, SrcF_add_right, sum_add_distrib, Loc2E_add])
    (fun r A B => by simp only [LS0, SrcF_smul_right, ← smul_sum, Loc2E_smul])

theorem LS_split (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N) (s : ℂ)
    (b : Fin d → ℕ) :
    LS j C V (fun b' => sigE s (W b')) b = LS0L j C (EthEL C) b V V + LpartL j C s b W := by
  simp only [LS, SX, Sb, LS0L, LinearMap.mk₂_apply, LS0, LpartL, LinearMap.coe_mk, AddHom.coe_mk,
    sum_add_distrib, Loc2E_add, SrcF, Vpr, VprL, EthEL_apply]

/-- The bilinear maps `β_{j,k} : ℂ⁴ × ℂ⁴ → ℂ⁴`. -/
def beta (j k : ℕ) (b : Fin d → ℕ) (i₀ : Fin d) :
    (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) :=
  if k = j then
    ((LS0L j (D.C j) (EthEL (D.C j)) b).compl₁₂ (VfamL j) (VfamL j)).compr₂
      (cvec4 (blockSet (L := L) (N := N) j b) i₀ ∘ₗ (Ev (Lam d L N)).val.toLinearMap)
  else
    ((SrcL k (D.C k) (EthEL (D.C k))).compl₁₂ (VfamL k) (VfamL k)).compr₂
      (cvec4 (blockSet (L := L) (N := N) j b) i₀ ∘ₗ (Ev (Lam d L N)).val.toLinearMap ∘ₗ
        LpartL j (D.C j) (D.s j) b ∘ₗ D.TrIt k (j - 1 - k))

/-- **`prop:C4b`(a)**: with the linearised remainder, the coefficient vector of
`Loc_{B_+,B} S_j(B_+)` is `∑_{k ≤ j} β_{j,k}(κ_k, κ_k)`. The bilinear maps `β_{j,k}` depend only
on `C k, …, C j` and `s (k+1), …, s j`. -/
theorem kappaS_quad (j : ℕ) (b : Fin d → ℕ) (i₀ : Fin d) :
    cvec4 (blockSet (L := L) (N := N) j b) i₀
      (LS j (D.C j) (D.Vin j) (fun b' => sigE (D.s j) (D.Wlin j b')) b : Alg d L N) =
      ∑ k ∈ range (j + 1), D.beta j k b i₀ (D.κ k).toVec (D.κ k).toVec := by
  rw [LS_split, D.Wlin_eq, map_sum, sum_range_succ, add_comm]
  simp only [Subalgebra.coe_add, AddSubmonoidClass.coe_finsetSum, map_add, map_sum]
  congr 1
  · refine sum_congr rfl fun k hk => ?_
    have hkj : k ≠ j := (mem_range.1 hk).ne
    simp only [beta, if_neg hkj, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
      LinearMap.comp_apply]
    rfl
  · simp only [beta, if_pos rfl, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
      LinearMap.comp_apply]
    rfl

/-- **`prop:C4b`(a) for the coupling vector**: if `Loc_{B_+,B} S_j(B_+)` is the coupling
polynomial `u|B| + V_{κ_S}(B)` (as it is by `LS_coup`), then `κ_S = ∑_{k ≤ j} β_{j,k}(κ_k, κ_k)`. -/
theorem kappaS_quad' (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) (i₀ : Fin d) {r : ℂ} {κS : Coup}
    (hS : (LS j (D.C j) (D.Vin j) (fun b' => sigE (D.s j) (D.Wlin j b')) b : Alg d L N) =
      unif r (coupC κS) (coupE κS) (blockSet j b)) :
    κS.toVec = ∑ k ∈ range (j + 1), D.beta j k b i₀ (D.κ k).toVec (D.κ k).toVec := by
  have hsm := isSmall_blockSet_of_mem hb
  rw [← D.kappaS_quad j b i₀, hS, cvec4_unif (patch_of_small hL hj hsm) hsm.2.1.1]

/-- The remainder from the products in `Wnext2` enters linearly:
`Loc S_j(𝒲) - Loc S_j(𝒲^lin) = Loc_{B_+,B} ∑ 𝔼θ σ (𝒲 - 𝒲^lin)`. -/
theorem LS_sub_lin (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W W' : Fam d L N) (s : ℂ)
    (b : Fin d → ℕ) :
    LS j C V (fun b' => sigE s (W b')) b - LS j C V (fun b' => sigE s (W' b')) b =
      LpartL j C s b (W - W') := by
  rw [LS_split, LS_split, map_sub]; abel

/-- `TrIt k n` depends only on `C`, `s` at the indices `k + 1, …, k + n`. -/
theorem TrIt_congr {D D' : FlowSeq d L N} (k : ℕ) :
    ∀ n, (∀ i, k + 1 ≤ i → i ≤ k + n → D.C i = D'.C i ∧ D.s i = D'.s i) →
      D.TrIt k n = D'.TrIt k n
  | 0, _ => rfl
  | n + 1, h => by
    have h1 := h (k + 1 + n) (by omega) (by omega)
    simp only [TrIt, h1.1, h1.2,
      TrIt_congr k n fun i hi hi' => h i hi (by omega)]

/-- `β_{j,k}` depends only on `C k, …, C j` and `s (k+1), …, s j`. -/
theorem beta_congr {D D' : FlowSeq d L N} {j k : ℕ} (hkj : k ≤ j)
    (hC : ∀ i, k ≤ i → i ≤ j → D.C i = D'.C i) (hs : ∀ i, k + 1 ≤ i → i ≤ j → D.s i = D'.s i)
    (b : Fin d → ℕ) (i₀ : Fin d) : D.beta j k b i₀ = D'.beta j k b i₀ := by
  unfold beta
  split_ifs with h
  · rw [hC j (by omega) le_rfl]
  · rw [hC j hkj le_rfl, hs j (by omega) le_rfl, hC k le_rfl hkj,
      TrIt_congr k (j - 1 - k) fun i hi hi' => ⟨hC i (by omega) (by omega),
        hs i hi (by omega)⟩]

end FlowSeq

end

end Step2
