import Step2.Coup.CoupQuad

/-!
# `β_{j,k}(κ, κ) = q_{j,k}(κ')` (`h02uv-outline.tex`, Proposition `prop:C4b`(a))

The source `½ F_C(𝔼θ V_κ(B), 𝔼θ V_κ(Λ))` equals `½ F_C(V_{κ'}(B), V_{κ'}(Λ))`, where `κ'` is the
first-order image of `κ` (`expLC_Vcoup`), because constants drop out of `F_C` (`FC_const_left`).
So `β_{j,k}(u, v) = β^q_{j,k}(κ'(u), κ'(v))` (`beta_eq_betaQ`). Here `β^q` is defined with the
pre-map `P = id` and the shift `u ↦ κ'(u)` is linear (`shiftL`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-! ### Constants drop out of `F` -/

theorem FC_const_left (C : Matrix (Lam d L N) (Lam d L N) ℂ) (r : ℂ) (B : Alg d L N) :
    FC C (r • (1 : Alg d L N)) B = 0 := by
  have h1 : expLC (-C) (r • (1 : Alg d L N)) = r • 1 := by rw [map_smul, expLC_one]
  have h2 : expLC C (expLC (-C) B) = B := by
    have := expLC_neg_expLC (-C) B
    rwa [neg_neg] at this
  rw [FC, h1, smul_mul_assoc, one_mul, map_smul, h2, smul_mul_assoc, one_mul, sub_self]

theorem FCE_add_const_left (C : Matrix (Lam d L N) (Lam d L N) ℂ) (r : ℂ)
    (A B : EvR (Lam d L N)) : FCE C (A + r • 1) B = FCE C A B := by
  refine Subtype.ext ?_
  simp only [coe_FCE, Subalgebra.coe_add, Subalgebra.coe_smul, OneMemClass.coe_one]
  rw [FC_add_left, FC_const_left, add_zero]

theorem FCE_add_const_right (C : Matrix (Lam d L N) (Lam d L N) ℂ) (r : ℂ)
    (A B : EvR (Lam d L N)) : FCE C A (B + r • 1) = FCE C A B := by
  rw [FCE_comm, FCE_add_const_left, FCE_comm]

/-! ### The first-order shift on `ℂ⁴` -/

/-- `κ ↦ κ' = (z - g c₀, y - g δ, ν + 2d g δ, g)` on `ℂ⁴`. -/
def shiftL (d : ℕ) (c₀ δ : ℂ) : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun v := ![v 0 - v 3 * c₀, v 1 - v 3 * δ, v 2 + 2 * d * v 3 * δ, v 3]
  map_add' v w := by funext a; fin_cases a <;> simp <;> ring
  map_smul' r v := by funext a; fin_cases a <;> simp <;> ring

/-- `𝔼_C θ V_v(B) = V_{v'}(B) + const`. -/
theorem EthE_VfamL {C : Matrix (Lam d L N) (Lam d L N) ℂ} {c₀ δ : ℂ}
    (hc₀ : ∀ x, C x x = c₀) (hδ : ∀ x e, C (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, C x (x + dirVec e) = c₀ + δ) (i : ℕ) (v : Fin 4 → ℂ) (b : Fin d → ℕ) :
    ∃ r : ℂ, EthE C (VfamL (L := L) (N := N) i v b) =
      VfamL i (shiftL d c₀ δ v) b + r • 1 := by
  obtain ⟨r, hr⟩ := expLC_Vcoup hc₀ hδ hδ' (Coup.ofVec v) (blockSet (L := L) (N := N) i b)
  refine ⟨r, Subtype.ext ?_⟩
  simp only [coe_EthE, Subalgebra.coe_add, Subalgebra.coe_smul, OneMemClass.coe_one]
  exact hr

/-- **The source in terms of `κ'`.** -/
theorem SrcF_shift {C : Matrix (Lam d L N) (Lam d L N) ℂ} {c₀ δ : ℂ}
    (hc₀ : ∀ x, C x x = c₀) (hδ : ∀ x e, C (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, C x (x + dirVec e) = c₀ + δ) (i : ℕ) (u v : Fin 4 → ℂ) (b : Fin d → ℕ) :
    SrcF i C (EthEL C) (VfamL i u) (VfamL i v) b =
      SrcF i C LinearMap.id (VfamL i (shiftL d c₀ δ u)) (VfamL i (shiftL d c₀ δ v)) b := by
  classical
  choose ru hru using fun b' => EthE_VfamL (L := L) (N := N) hc₀ hδ hδ' i u b'
  choose rv hrv using fun b' => EthE_VfamL (L := L) (N := N) hc₀ hδ hδ' i v b'
  simp only [SrcF, EthEL_apply, LinearMap.id_apply, hru, hrv, sum_add_distrib, ← sum_smul,
    FCE_add_const_left, FCE_add_const_right]

theorem SrcFam_shift {C : Matrix (Lam d L N) (Lam d L N) ℂ} {c₀ δ : ℂ}
    (hc₀ : ∀ x, C x x = c₀) (hδ : ∀ x e, C (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, C x (x + dirVec e) = c₀ + δ) (i : ℕ) (u v : Fin 4 → ℂ) :
    SrcL i C (EthEL C) (VfamL i u) (VfamL i v) =
      SrcL i C LinearMap.id (VfamL i (shiftL d c₀ δ u)) (VfamL i (shiftL d c₀ δ v)) := by
  rw [SrcL_apply, SrcL_apply]
  funext c
  simp only [SrcFam, SrcF_shift hc₀ hδ hδ']

theorem LS0_shift {C : Matrix (Lam d L N) (Lam d L N) ℂ} {c₀ δ : ℂ}
    (hc₀ : ∀ x, C x x = c₀) (hδ : ∀ x e, C (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, C x (x + dirVec e) = c₀ + δ) (j : ℕ) (b : Fin d → ℕ) (u v : Fin 4 → ℂ) :
    FlowSeq.LS0L j C (EthEL C) b (VfamL j u) (VfamL j v) =
      FlowSeq.LS0L j C LinearMap.id b (VfamL j (shiftL d c₀ δ u)) (VfamL j (shiftL d c₀ δ v)) := by
  simp only [FlowSeq.LS0L, LinearMap.mk₂_apply, FlowSeq.LS0, SrcF_shift hc₀ hδ hδ']

namespace FlowSeq

variable (D : FlowSeq d L N)

/-- `β^q_{j,k}`: the same as `β_{j,k}`, with the source `½ F(V_κ(B), V_λ(Λ))` (no `𝔼θ`). -/
def betaQ (j k : ℕ) (b : Fin d → ℕ) (i₀ : Fin d) :
    (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) :=
  if k = j then
    ((LS0L j (D.C j) LinearMap.id b).compl₁₂ (VfamL j) (VfamL j)).compr₂
      (cvec4 (blockSet (L := L) (N := N) j b) i₀ ∘ₗ (Ev (Lam d L N)).val.toLinearMap)
  else
    ((SrcL k (D.C k) LinearMap.id).compl₁₂ (VfamL k) (VfamL k)).compr₂
      (cvec4 (blockSet (L := L) (N := N) j b) i₀ ∘ₗ (Ev (Lam d L N)).val.toLinearMap ∘ₗ
        LpartL j (D.C j) (D.s j) b ∘ₗ D.TrIt k (j - 1 - k))

/-- **`β_{j,k}(u, v) = β^q_{j,k}(u', v')`**, with `'` the first-order shift of `C k`. -/
theorem beta_eq_betaQ {j k : ℕ} {c₀ δ : ℂ} (hc₀ : ∀ x, D.C k x x = c₀)
    (hδ : ∀ x e, D.C k (x + dirVec e) x = c₀ + δ) (hδ' : ∀ x e, D.C k x (x + dirVec e) = c₀ + δ)
    (b : Fin d → ℕ) (i₀ : Fin d) (u v : Fin 4 → ℂ) :
    D.beta j k b i₀ u v = D.betaQ j k b i₀ (shiftL d c₀ δ u) (shiftL d c₀ δ v) := by
  unfold beta betaQ
  split_ifs with h
  · subst h
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LS0_shift hc₀ hδ hδ']
  · simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, SrcFam_shift hc₀ hδ hδ']

/-- **`prop:C4b`(a) in terms of `κ'`**: `κ_S^lin = ∑_{k ≤ j} β^q_{j,k}(κ'_k, κ'_k)`. -/
theorem kappaS_quadQ (j : ℕ) (b : Fin d → ℕ) (i₀ : Fin d) (c₀ δ : ℕ → ℂ)
    (hc₀ : ∀ k x, D.C k x x = c₀ k) (hδ : ∀ k x e, D.C k (x + dirVec e) x = c₀ k + δ k)
    (hδ' : ∀ k x e, D.C k x (x + dirVec e) = c₀ k + δ k) :
    cvec4 (blockSet (L := L) (N := N) j b) i₀
      (LS j (D.C j) (D.Vin j) (fun b' => sigE (D.s j) (D.Wlin j b')) b : Alg d L N) =
      ∑ k ∈ range (j + 1), D.betaQ j k b i₀ (shiftL d (c₀ k) (δ k) (D.κ k).toVec)
        (shiftL d (c₀ k) (δ k) (D.κ k).toVec) := by
  rw [D.kappaS_quad]
  exact sum_congr rfl fun k _ => D.beta_eq_betaQ (hc₀ k) (hδ k) (hδ' k) b i₀ _ _

end FlowSeq

end

end Step2
