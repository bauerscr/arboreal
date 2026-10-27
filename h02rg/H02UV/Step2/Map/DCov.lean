import Step2.Map.FullStep
import DressedFRD

/-!
# The dressed covariances along the flow (`h02uv-outline.tex`, Proposition `prop:C5`)

For DressedFRD data `D` on `Λ_N` and `j + 1 < N`, the covariance
`C'_{j+1} = Z_{j+1} Γ^int_{j+1}` (the matrix `kmat (Z_{j+1} • Γ^int_{j+1})`) satisfies:

* `goodCov2_dressed`: `GoodCov2` at scale `j`, with field scale
  `ℓ = (c_S + K |ζ|_{≤j})^{1/2} L^{-j(d-2)/2} L^{p_Φ}`. The factor `L^{p_Φ}` comes from passing
  from the derivative scale `L^j` of `cor_gram` to the scale `L^{j+1}` of `GoodCov2`
  (`GramBound.rescale`).
* `kmat_CSym`, `kmat_symm`: invariance under the generated lattice automorphisms and symmetry,
  when the symbol is invariant under the signed permutations of momenta (`symSub`). This holds
  for `Γ^int_{j+1}` if it holds for the `C_k` (`Gint_symMem`), and for the `C_k` of
  `DressedFRD.frdC` (`frdC_symm`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

/-! ### Rescaling a Gram bound -/

section Rescale

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] [AddAction (E → ℕ) Λ]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A Gram bound at derivative scale `h` gives one at scale `c h`, `c ≥ 1`, with `ℓ c^p`. -/
theorem GramBound.rescale {p : ℕ} {h ℓ c : ℝ} (hh : 0 < h) (hc : 1 ≤ c) {Fv Gv : Λ → H}
    (hB : GramBound E p h ℓ Fv Gv) : GramBound E p (c * h) (ℓ * c ^ p) Fv Gv := by
  intro a ha x
  obtain ⟨h1, h2⟩ := hB a ha x
  have hk : 0 < (h ^ mabs a)⁻¹ := by positivity
  have hℓ : 0 ≤ ℓ := by
    by_contra hneg
    have : ℓ * (h ^ mabs a)⁻¹ < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hk
    linarith [norm_nonneg (gvec Fv (dprof a x))]
  have hx : (h ^ mabs a)⁻¹ ≤ c ^ p * ((c * h) ^ mabs a)⁻¹ := by
    rw [mul_pow, mul_inv, ← mul_assoc]
    refine le_mul_of_one_le_left hk.le ?_
    rw [← div_eq_mul_inv, one_le_div (by positivity)]
    exact pow_le_pow_right₀ hc ha
  have key : ℓ * (h ^ mabs a)⁻¹ ≤ ℓ * c ^ p * ((c * h) ^ mabs a)⁻¹ :=
    (mul_le_mul_of_nonneg_left hx hℓ).trans_eq (by ring)
  exact ⟨h1.trans key, h2.trans key⟩

end Rescale

/-! ### `GoodCov2` from DressedFRD -/

variable {d L N : ℕ} [NeZero L]

/-- `C'_{j+1} = Z_{j+1} Γ^int_{j+1}` as a matrix on `Λ_N`. -/
abbrev Cdr (D : DressedFRD.Data d (L ^ N)) (j : ℕ) : Matrix (Lam d L N) (Lam d L N) ℂ :=
  DressedFRD.kmat (D.Z (j + 1) • D.Gint j)

/-- The field scale of `prop:C5`. -/
def ellDr (d L : ℕ) (cS K M : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (cS + K * M) * (L : ℝ) ^ (-((j : ℝ) * ((d : ℝ) - 2)) / 2) * (L : ℝ) ^ pPhi d

/-- **`prop:C5`, Gram part and range**: `C'_{j+1}` satisfies `GoodCov2` at scale `j`. -/
theorem goodCov2_dressed {q M : ℕ} {cS ζbar K : ℝ} (D : DressedFRD.Data d (L ^ N))
    (hDL : D.L = L) (hDN : D.N = N) (hS : DressedFRD.StdFull D.L D.N q M D.msq cS D.C)
    (hL : 1 ≤ L) (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 2) {j : ℕ} (hc : D.Concl q ζbar K j)
    (hj : j + 1 < N) (hpq : 2 * pPhi d ≤ q) :
    GoodCov2 (d := d) (L := L) (N := N) j (ellDr d L cS K (D.Mz (j + 1)) j) (Cdr D j) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hjD : j + 1 < D.N := by rw [hDN]; exact hj
  have hg := DressedFRD.Data.cor_gram hS (by rw [hDL]; exact hL) hζ hc hjD
  rw [← DressedFRD.snorm_smul (by rw [hDL]; exact hL0), hDL] at hg
  constructor
  · refine ⟨_, inferInstance, inferInstance, DressedFRD.gramF (D.Z (j + 1) • D.Gint j),
      DressedFRD.gramG (D.Z (j + 1) • D.Gint j), DressedFRD.kmat_isGram _, ?_⟩
    have hB := DressedFRD.kmat_gramBound (L := (L : ℝ)) (p := pPhi d) hL0 hpq hg
    have hB' := GramBound.rescale (c := (L : ℝ)) (by positivity) (by exact_mod_cast hL) hB
    rw [← pow_succ'] at hB'
    exact hB'
  · intro _ x y hxy
    have hr := hc.range hjD
    rw [hDL] at hr
    have h1 := DressedFRD.rng_smul_le (D.Z (j + 1)) (D.Gint j)
    refine DressedFRD.kern_eq_zero_of_rng_lt ?_
    have h2 : (2 * DressedFRD.rng (D.Z (j + 1) • D.Gint j) : ℝ) < (L : ℝ) ^ (j + 1) := by
      exact_mod_cast (by omega : 2 * DressedFRD.rng (D.Z (j + 1) • D.Gint j) < L ^ (j + 1))
    have h3 : ((DressedFRD.rng (D.Z (j + 1) • D.Gint j) : ℕ) : ℝ) <
        ((supNorm (x - y) : ℕ) : ℝ) := by
      linarith
    exact_mod_cast h3

/-! ### Lattice symmetry -/

section SymSub

variable {n : ℕ} [NeZero n]

/-- Symbols invariant under the signed permutations of momenta. -/
def symSub : Subring (DressedFRD.Sym d n) where
  carrier := {w | ∀ (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) m, w (symmDual π s m) = w m}
  mul_mem' {a b} ha hb π s m := by simp only [Pi.mul_apply, ha π s m, hb π s m]
  one_mem' π s m := rfl
  add_mem' {a b} ha hb π s m := by simp only [Pi.add_apply, ha π s m, hb π s m]
  zero_mem' π s m := rfl
  neg_mem' {a} ha π s m := by simp only [Pi.neg_apply, ha π s m]

theorem smul_symMem (c : ℂ) {w : DressedFRD.Sym d n} (hw : w ∈ symSub) : c • w ∈ symSub :=
  fun π s m => by simp only [Pi.smul_apply, hw π s m]

theorem const_symMem (c : ℂ) : (fun _ => c : DressedFRD.Sym d n) ∈ symSub := fun _ _ _ => rfl

theorem div_symMem {v w : DressedFRD.Sym d n} (hv : v ∈ symSub) (hw : w ∈ symSub) :
    (fun m => v m / w m) ∈ symSub := fun π s m => by simp only [hv π s m, hw π s m]

theorem ofR_symMem {f : Torus d n → ℝ} (hf : ∀ π s m, f (symmDual π s m) = f m) :
    DressedFRD.ofR f ∈ symSub := fun π s m => by simp [DressedFRD.ofR, hf]

theorem Asym_symMem (msq : ℝ) : DressedFRD.Asym (d := d) (n := n) msq ∈ symSub :=
  fun π s m => by simp [DressedFRD.Asym, lam_symmDual]

variable {C : ℕ → Torus d n → ℝ} (hC : ∀ k π s m, C k (symmDual π s m) = C k m)
include hC

theorem Cle_symMem (j : ℕ) : DressedFRD.Cle C j ∈ symSub :=
  Subring.sum_mem _ fun k _ => ofR_symMem (hC k)

theorem Cgt_symMem (N j : ℕ) : DressedFRD.Cgt C N j ∈ symSub :=
  Subring.sum_mem _ fun k _ => ofR_symMem (hC k)

theorem Ehat_symMem (msq : ℝ) (j : ℕ) : DressedFRD.Ehat msq C j ∈ symSub :=
  Subring.mul_mem _ (Asym_symMem msq) (Cle_symMem hC j)

end SymSub

namespace DData

open DressedFRD DressedFRD.Data

variable {n : ℕ} [NeZero n] {D : Data d n}
  (hC : ∀ k π s m, D.C k (symmDual π s m) = D.C k m)
include hC

theorem letV_symMem {j : ℕ} {R : ℕ → Sym d n} (hR : ∀ r, R r ∈ symSub) (κ : Fin 3)
    (ℓ : Option ℕ) : D.letV j R κ ℓ ∈ symSub := by
  have hA := Asym_symMem (d := d) (n := n) D.msq
  rcases ℓ with _ | r <;> fin_cases κ
  · exact Cle_symMem hC j
  · exact Subring.sub_mem _ (Subring.one_mem _) (Ehat_symMem hC _ j)
  · exact Ehat_symMem hC _ j
  · exact Subring.neg_mem _ (smul_symMem _ (hR r))
  · exact smul_symMem _ (Subring.mul_mem _ hA (hR r))
  · exact Subring.neg_mem _ (smul_symMem _ (Subring.mul_mem _ hA (hR r)))

theorem eps_symMem {j : ℕ} {R : ℕ → Sym d n} (hR : ∀ r, R r ∈ symSub) : D.eps j R ∈ symSub :=
  Subring.sub_mem _ (Ehat_symMem hC _ j) (Subring.sum_mem _ fun r _ =>
    smul_symMem _ (Subring.mul_mem _ (Asym_symMem _) (hR r)))

theorem wLen_symMem {j : ℕ} {R : ℕ → Sym d n} (hR : ∀ r, R r ∈ symSub) (s k : ℕ) :
    D.wLen j R s k ∈ symSub :=
  Subring.sum_mem _ fun w _ => Subring.prod_mem _ fun i _ => letV_symMem hC hR _ _

theorem wLow_symMem {j : ℕ} {R : ℕ → Sym d n} (hR : ∀ r, R r ∈ symSub) (s : ℕ) :
    D.wLow j R s ∈ symSub :=
  Subring.sum_mem _ fun k _ => smul_symMem _ (wLen_symMem hC hR s k)

theorem wTot_symMem {j : ℕ} {R : ℕ → Sym d n} (hR : ∀ r, R r ∈ symSub) :
    D.wTot j R ∈ symSub := by
  have he := eps_symMem hC (j := j) hR
  have hc := const_symMem (d := d) (n := n) (D.zp j)
  have hA := Asym_symMem (d := d) (n := n) D.msq
  have hAi : (fun m => (Asym D.msq m)⁻¹ : Sym d n) ∈ symSub := by
    have := div_symMem (Subring.one_mem symSub) hA
    simpa only [Pi.one_apply, one_div] using this
  have hnum := Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hc hAi) he)
    (Subring.sub_mem _ (Subring.one_mem _) he)
  have hden := Subring.sub_mem _ (Subring.one_mem _) (Subring.mul_mem _ hc he)
  exact div_symMem hnum hden

theorem wSc_symMem {j : ℕ} {R : ℕ → Sym d n} (hR : ∀ r, R r ∈ symSub) (s : ℕ) :
    D.wSc j R s ∈ symSub := by
  unfold wSc wTop
  split_ifs
  · exact wLow_symMem hC hR s
  · exact Subring.sub_mem _ (wTot_symMem hC hR)
      (Subring.sum_mem _ fun s _ => wLow_symMem hC hR s)

theorem tails_symMem : ∀ j r, D.tails j r ∈ symSub
  | 0, _ => Subring.zero_mem _
  | j + 1, r => by
    have ih := tails_symMem j
    unfold tails
    split_ifs
    · exact smul_symMem _ (Subring.add_mem _ (smul_symMem _ (ih r)) (wSc_symMem hC ih r))
    · exact Subring.zero_mem _

theorem Gam_symMem (j : ℕ) : D.Gam j ∈ symSub :=
  Subring.add_mem _ (smul_symMem _ (Cgt_symMem hC _ j))
    (Subring.sum_mem _ fun r _ => tails_symMem hC j r)

/-- `Γ^int_{j+1}` is invariant under the signed permutations of momenta. -/
theorem Gint_symMem (j : ℕ) : D.Gint j ∈ symSub := by
  have hR := tails_symMem hC (D := D) j
  unfold Gint
  split_ifs
  · exact smul_symMem _ (Subring.add_mem _ (Subring.add_mem _
      (ofR_symMem (hC _)) (smul_symMem _ (hR _))) (wSc_symMem hC hR _))
  · have hG := Gam_symMem hC (D := D) j
    have hz := const_symMem (d := d) (n := n) (D.ζ j * D.Z j)
    exact div_symMem hG (Subring.add_mem _ (Subring.one_mem _)
      (Subring.mul_mem _ (Subring.mul_mem _ hz (Asym_symMem _)) hG))

end DData

/-- The symbols of `DressedFRD.frdC` are invariant under the signed permutations. -/
theorem frdC_symm (P : PtFamily) {n : ℕ} [NeZero n] (msq : ℝ) (L' N' k : ℕ)
    (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) (m : Torus d n) :
    DressedFRD.frdC P msq L' N' k (symmDual π s m) = DressedFRD.frdC P msq L' N' k m := by
  unfold DressedFRD.frdC
  split_ifs <;> simp [FRD.wt, uhat_symmDual]

/-! ### The matrix of an invariant symbol -/

theorem kern_symm' {n : ℕ} [NeZero n] {w : DressedFRD.Sym d n} (hw : w ∈ symSub)
    (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) (z : Torus d n) :
    DressedFRD.kern w (FRD.symm π s z) = DressedFRD.kern w z := by
  simp only [DressedFRD.kern, char_symm]
  congr 1
  exact Fintype.sum_bijective _ (symmDual_bijective π s) _ _ fun m => by rw [hw π s m]

theorem kmat_CSym {w : DressedFRD.Sym d (L ^ N)} (hw : w ∈ symSub) :
    CSym (d := d) (L := L) (N := N) (DressedFRD.kmat w) := by
  intro T hT x y
  obtain ⟨π, s, t, h⟩ := hT.exists_form
  rw [h, h]
  show DressedFRD.kern w ((FRD.symm π s x + t) - (FRD.symm π s y + t)) = DressedFRD.kern w (x - y)
  rw [add_sub_add_right_eq_sub, ← symm_sub]
  exact kern_symm' hw π s (x - y)

theorem kmat_symm {w : DressedFRD.Sym d (L ^ N)} (hw : w ∈ symSub) (x y : Lam d L N) :
    DressedFRD.kmat w x y = DressedFRD.kmat w y x := by
  simp only [DressedFRD.kmat]
  have e : FRD.symm (n := L ^ N) 1 (fun _ => -1) (x - y) = y - x := by
    funext i
    simp only [FRD.symm, co, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul,
      Equiv.Perm.coe_one, id]
    exact congrFun (neg_sub x y) i
  rw [← e, kern_symm' hw]

/-! ### `prop:C5` -/

theorem Cdr_CSym {D : DressedFRD.Data d (L ^ N)}
    (hC : ∀ k π s m, D.C k (symmDual π s m) = D.C k m) (j : ℕ) :
    CSym (d := d) (L := L) (N := N) (Cdr D j) :=
  kmat_CSym (smul_symMem _ (DData.Gint_symMem hC j))

theorem Cdr_symm {D : DressedFRD.Data d (L ^ N)}
    (hC : ∀ k π s m, D.C k (symmDual π s m) = D.C k m) (j : ℕ) (x y : Lam d L N) :
    Cdr D j x y = Cdr D j y x :=
  kmat_symm (smul_symMem _ (DData.Gint_symMem hC j)) x y

/-- **`prop:C5`** for the decomposition of `FRD`: there are `c_S`, `ζ̄` and `K` such that, for
`|ζ_i| ≤ ζ̄` and `j + 1 < N`, `C'_{j+1} = Z_{j+1} Γ^int_{j+1}` satisfies `GoodCov2` at scale `j`
with `ℓ = (c_S + K |ζ|_{≤j})^{1/2} L^{-j(d-2)/2} L^{p_Φ}`, is invariant under the lattice
symmetries, and is symmetric. -/
theorem prop_C5 (P : PtFamily) (hd : 2 ≤ d) (hL7 : 7 ≤ L) :
    ∃ cS : ℝ, 0 ≤ cS ∧ ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, ∀ (N : ℕ) (msq : ℝ)
      (ζ : ℕ → ℂ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
      (∀ i, ‖ζ i‖ ≤ ζbar) → ∀ j, j + 1 < N →
      let D : DressedFRD.Data d (L ^ N) := ⟨L, N, msq, DressedFRD.frdC P msq L N, ζ⟩
      GoodCov2 (d := d) (L := L) (N := N) j (ellDr d L cS K (D.Mz (j + 1)) j) (Cdr D j) ∧
        CSym (d := d) (L := L) (N := N) (Cdr D j) ∧ ∀ x y, Cdr D j x y = Cdr D j y x := by
  have hq : 2 ≤ 2 * pPhi d := by simp only [pPhi]; omega
  obtain ⟨cS, hcS, hS⟩ := DressedFRD.frd_stdFull P (d := d) hd hL7 (q := 2 * pPhi d)
    (M := 2 * pPhi d + d + 1) le_rfl
  obtain ⟨ζbar, hζ, hζ8, K, hK⟩ := DressedFRD.thm_main_hol (d := d) hd hq hL7
    (M := 2 * pPhi d + d + 1) le_rfl hcS
  refine ⟨cS, hcS, ζbar, hζ, hζ8, K, fun N msq ζ hN hmsq hmsq' hζi j hj => ?_⟩
  intro D
  have hS' := hS (L ^ N) N msq hN rfl hmsq
  have h := hK (L ^ N) D rfl rfl hS' hmsq'
  have hc := h.1 hζi j (by simp only [D]; omega)
  have hC : ∀ k π s m, D.C k (symmDual π s m) = D.C k m := fun k π s m => frdC_symm P _ _ _ _ π s m
  refine ⟨goodCov2_dressed D rfl rfl hS' (by omega) (fun i => (hζi i).trans (by linarith)) hc hj
    le_rfl, Cdr_CSym hC j, Cdr_symm hC j⟩

end

end Step2
